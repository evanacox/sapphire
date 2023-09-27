//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::{ArenaKey, SecondaryMap};
use crate::codegen::regalloc::allocator::{defs, uses, RegisterMapping};
use crate::codegen::{
    Allocation, Architecture, MIRFunction, MachInst, PReg, ProgramPoint, Reg, RegClass,
    RegisterAllocator, SpillReload, StackFrame, VariableLocation,
};
use smallvec::SmallVec;
use std::mem;

/// A "register allocator" that puts everything on the stack, only loading
/// values to perform operations.
///
/// This is an extremely fast allocator, but it generates awful code (and is
/// only made worse by any code generators that generate extraneous `mov`s).
pub struct StackRegAlloc {
    spills: Vec<(ProgramPoint, SpillReload)>,
    mapping: RegisterMapping,
    spilled_regs: SecondaryMap<Reg, VariableLocation>,
    temporary_int_regs: Vec<PReg>,
    temporary_float_regs: Vec<PReg>,
    taken_temporary_int_regs: SmallVec<[PReg; 4]>,
    taken_temporary_float_regs: SmallVec<[PReg; 4]>,
}

impl StackRegAlloc {
    fn order_temporaries<Arch: Architecture>(&mut self, frame: &mut dyn StackFrame<Arch>) {
        // we exclusively use clobbered registers, we spill everything anyway
        // so we may as well not necessitate preserving registers
        for &reg in frame.registers().clobbered.0.iter().rev() {
            self.temporary_int_regs.push(reg);
        }

        for &reg in frame.registers().clobbered.1.iter().rev() {
            self.temporary_float_regs.push(reg);
        }
    }

    fn take_temporary(&mut self, class: RegClass) -> PReg {
        match class {
            RegClass::Int => {
                let p_reg = self
                    .temporary_int_regs
                    .pop()
                    .expect("how did we get run out of temporaries?");

                self.taken_temporary_int_regs.push(p_reg);

                p_reg
            }
            RegClass::Float => {
                let p_reg = self
                    .temporary_float_regs
                    .pop()
                    .expect("how did we get run out of temporaries?");

                self.taken_temporary_float_regs.push(p_reg);

                p_reg
            }
        }
    }

    fn return_temporaries(&mut self) {
        // we keep two stacks, one of the available registers and one
        // of the taken registers. when we return our temporaries,
        // we restore the original complete set of registers in
        // their original order
        while let Some(preg) = self.taken_temporary_int_regs.pop() {
            self.temporary_int_regs.push(preg);
        }

        while let Some(preg) = self.taken_temporary_float_regs.pop() {
            self.temporary_float_regs.push(preg);
        }
    }

    fn allocate<Arch: Architecture>(
        mut self,
        program: &MIRFunction<Arch::Inst>,
        frame: &mut dyn StackFrame<Arch>,
    ) -> Allocation {
        self.order_temporaries(frame);

        let mut mapping = SmallVec::default();

        // basic idea: for the entire program, go over every instruction and check the following:
        //
        //   1. if the instruction is a `x <- preg` we spill X after the `mov`
        //   2. if the instruction is a `preg <- x` we do a reload and mov into the preg
        //   3. if the instruction is a `preg <- preg` we don't touch it
        //   4. for all other instructions, we load all operands and then store all modified (virtual) registers.
        //
        for (i, &inst) in program.all_instructions().iter().enumerate() {
            let before = ProgramPoint::key_new(i);
            let after = ProgramPoint::key_new(i + 1);

            if let Some(mov) = inst.as_copy() {
                match (mov.from.as_preg(), mov.to.to_reg().as_preg()) {
                    // case #1, need to spill `to`
                    (Some(from), None) => {
                        let t1 = self.take_temporary(from.class());

                        self.spill(after, frame, mov.to.to_reg(), t1);
                        mapping.push((mov.from, from));
                        mapping.push((mov.to.to_reg(), t1));
                    }
                    // case #2, need to reload `from`
                    (None, Some(to)) => {
                        let t1 = self.take_temporary(to.class());

                        self.reload(before, frame, mov.from, t1);
                        mapping.push((mov.from, t1));
                        mapping.push((mov.to.to_reg(), to));
                    }
                    // case #3, don't do anything
                    (Some(from), Some(to)) => {
                        mapping.push((mov.from, from));
                        mapping.push((mov.to.to_reg(), to));
                    }
                    // case #4 with a copy, `x2 <- x1`, need to reload x1 and spill x2
                    (None, None) => {
                        let t1 = self.take_temporary(mov.from.class());
                        let t2 = self.take_temporary(mov.from.class());

                        self.reload(before, frame, mov.from, t1);
                        self.spill(after, frame, mov.to.to_reg(), t2);
                        mapping.push((mov.from, t1));
                        mapping.push((mov.to.to_reg(), t2));
                    }
                }
            } else {
                // case #4, we just reload all (virtual) uses and spill all (virtual) defs
                let uses = uses!(inst, frame);

                for reg in uses.iter().copied() {
                    if reg.is_vreg() {
                        // we need to be careful not to take a temporary that is used
                        // by the instruction, or we'll break the behavior of the code
                        let tmp = loop {
                            let reg = self.take_temporary(reg.class());

                            if !uses.iter().any(|r| *r == Reg::from_preg(reg)) {
                                break reg;
                            }
                        };

                        self.reload(before, frame, reg, tmp);
                        mapping.push((reg, tmp));
                    } else {
                        // self.reload(before, frame, reg, reg.as_preg().unwrap());
                        mapping.push((reg, reg.as_preg().unwrap()))
                    }
                }

                for reg in defs!(inst, frame) {
                    if reg.is_vreg() {
                        let matching_temporary: Option<(Reg, PReg)> = mapping
                            .as_slice()
                            .iter()
                            .find(|&&(vreg, _)| vreg == reg)
                            .copied();

                        let tmp = match matching_temporary {
                            Some((_, tmp)) => tmp,
                            None => {
                                let tmp = self.take_temporary(reg.class());

                                // if we didn't find a mapping earlier, we need to add it ourselves
                                mapping.push((reg, tmp));

                                tmp
                            }
                        };

                        self.spill(after, frame, reg, tmp);
                    }
                }
            }

            self.return_temporaries();
            self.mapping.push(before, mem::take(&mut mapping))
        }

        Allocation {
            spills: mem::take(&mut self.spills),
            mapping: mem::replace(&mut self.mapping, RegisterMapping::new()),
        }
    }

    fn stack_space_for<Arch: Architecture>(
        &mut self,
        frame: &mut dyn StackFrame<Arch>,
        reg: Reg,
    ) -> VariableLocation {
        match self.spilled_regs.get(reg) {
            Some(loc) => *loc,
            None => {
                let loc = frame.spill_slot(8);

                self.spilled_regs.insert(reg, loc);

                loc
            }
        }
    }

    fn spill<Arch: Architecture>(
        &mut self,
        pp: ProgramPoint,
        frame: &mut dyn StackFrame<Arch>,
        reg: Reg,
        tmp: PReg,
    ) {
        let loc = self.stack_space_for(frame, reg);

        self.spills
            .push((pp, SpillReload::Spill { from: tmp, to: loc }))
    }

    fn reload<Arch: Architecture>(
        &mut self,
        pp: ProgramPoint,
        frame: &mut dyn StackFrame<Arch>,
        reg: Reg,
        tmp: PReg,
    ) {
        let loc = self.stack_space_for(frame, reg);

        self.spills
            .push((pp, SpillReload::Reload { from: loc, to: tmp }))
    }
}

impl Default for StackRegAlloc {
    fn default() -> Self {
        Self {
            spills: Vec::default(),
            mapping: RegisterMapping::new(),
            spilled_regs: SecondaryMap::default(),
            temporary_int_regs: Vec::default(),
            temporary_float_regs: Vec::default(),
            taken_temporary_int_regs: SmallVec::default(),
            taken_temporary_float_regs: SmallVec::default(),
        }
    }
}

impl<Arch: Architecture> RegisterAllocator<Arch> for StackRegAlloc {
    fn allocate(program: &MIRFunction<Arch::Inst>, frame: &mut dyn StackFrame<Arch>) -> Allocation {
        StackRegAlloc::default().allocate(program, frame)
    }
}
