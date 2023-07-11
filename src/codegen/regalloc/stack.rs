//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::SecondaryMap;
use crate::codegen::regalloc::allocator::{defs, uses, RegisterMapping};
use crate::codegen::{
    Allocation, Architecture, MIRFunction, MachInst, PReg, ProgramPoint, Reg, RegisterAllocator,
    SpillReload, StackFrame, VariableLocation, WriteableReg,
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
    temporary_regs: Vec<PReg>,
    taken_temporary_regs: SmallVec<[PReg; 4]>,
}

impl StackRegAlloc {
    fn stack_space_for<Arch: Architecture>(
        &mut self,
        frame: &mut dyn StackFrame<Arch>,
        reg: Reg,
        width: usize,
    ) -> VariableLocation {
        match self.spilled_regs.get(reg) {
            Some(loc) => *loc,
            None => {
                let loc = frame.spill_slot(width);

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
        width: usize,
    ) {
        let loc = self.stack_space_for(frame, reg, width);

        self.spills.push((
            pp,
            SpillReload::Spill {
                from: tmp,
                to: loc,
                width,
            },
        ))
    }

    fn reload<Arch: Architecture>(
        &mut self,
        pp: ProgramPoint,
        frame: &mut dyn StackFrame<Arch>,
        reg: Reg,
        tmp: PReg,
        width: usize,
    ) {
        let loc = self.stack_space_for(frame, reg, width);

        self.spills.push((
            pp,
            SpillReload::Reload {
                from: loc,
                to: tmp,
                width,
            },
        ))
    }

    fn order_temporaries<Arch: Architecture>(&mut self, frame: &mut dyn StackFrame<Arch>) {
        // we exclusively use clobbered registers, we spill everything anyway
        // so we may as well not necessitate preserving registers
        for &reg in frame.register_priority().clobbered.iter().rev() {
            self.temporary_regs.push(reg);
        }
    }

    fn take_temporary(&mut self) -> PReg {
        let preg = self
            .temporary_regs
            .pop()
            .expect("how did we get run out of temporaries?");

        self.taken_temporary_regs.push(preg);

        preg
    }

    fn return_temporaries(&mut self) {
        // we keep two stacks, one of the available registers and one
        // of the taken registers. when we return our temporaries,
        // we restore the original complete set of registers in
        // their original order
        while let Some(preg) = self.taken_temporary_regs.pop() {
            self.temporary_regs.push(preg);
        }
    }
}

impl Default for StackRegAlloc {
    fn default() -> Self {
        Self {
            spills: Vec::default(),
            mapping: RegisterMapping::new(),
            spilled_regs: SecondaryMap::default(),
            temporary_regs: Vec::default(),
            taken_temporary_regs: SmallVec::default(),
        }
    }
}

impl<Arch: Architecture> RegisterAllocator<Arch> for StackRegAlloc {
    fn allocate(
        &mut self,
        program: &MIRFunction<Arch::Inst>,
        frame: &mut dyn StackFrame<Arch>,
    ) -> Allocation {
        // replace self with default state
        mem::take(self);
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
            let before = ProgramPoint(i as u32);
            let after = ProgramPoint((i + 1) as u32);

            if let Some(mov) = inst.as_move() {
                match (mov.from.as_preg(), mov.to.to_reg().as_preg()) {
                    // case #1, need to spill `to`
                    (Some(from), None) => {
                        let t1 = self.take_temporary();

                        self.spill(after, frame, mov.to.to_reg(), t1, mov.width);
                        mapping.push((mov.from, from));
                        mapping.push((mov.to.to_reg(), t1));
                    }
                    // case #2, need to reload `from`
                    (None, Some(to)) => {
                        let t1 = self.take_temporary();

                        self.reload(before, frame, mov.from, t1, mov.width);
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
                        let t1 = self.take_temporary();
                        let t2 = self.take_temporary();

                        self.reload(before, frame, mov.from, t1, mov.width);
                        self.spill(after, frame, mov.to.to_reg(), t2, mov.width);
                        mapping.push((mov.from, t1));
                        mapping.push((mov.to.to_reg(), t2));
                    }
                }
            } else {
                // case #4, we just reload all (virtual) uses and spill all (virtual) defs
                for (reg, width) in uses!(inst, frame) {
                    if reg.is_vreg() {
                        let tmp = self.take_temporary();

                        self.reload(before, frame, reg, tmp, width as usize);
                        mapping.push((reg, tmp));
                    } else {
                        mapping.push((reg, reg.as_preg().unwrap()))
                    }
                }

                for (reg, width) in defs!(inst, frame) {
                    if reg.is_vreg() {
                        let matching_temporary: Option<(Reg, PReg)> = mapping
                            .as_slice()
                            .iter()
                            .find(|&&(vreg, _)| vreg == reg)
                            .copied();

                        let tmp = match matching_temporary {
                            Some((_, tmp)) => tmp,
                            None => {
                                let tmp = self.take_temporary();

                                // if we didn't find a mapping earlier, we need to add it ourselves
                                mapping.push((reg, tmp));

                                tmp
                            }
                        };

                        self.spill(after, frame, reg, tmp, width as usize);
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
}
