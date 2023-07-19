//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::{Architecture, FramelessCtx, PReg, Reg, WriteableReg};
use crate::ir;
use crate::ir::{FunctionMetadata, StackSlot, Value};

/// The location of a single "variable." This denotes something at the ABI level,
/// e.g. `stackslot`s, parameters and the like. This identifies where they are
/// in a way that the code generator can understand.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum VariableLocation {
    /// Says that a variable is located in a register
    InReg(Reg),
    /// Says that a variable is located at an offset relative to the frame pointer after
    /// the canonical prologue has executed.
    RelativeToFP(i32),
    /// Says that a variable is located at an offset relative to the stack pointer after
    /// the canonical prologue has executed.
    RelativeToSP(i32),
}

/// A representation of the specific available registers on a particular ABI.
pub struct AvailableRegisters {
    /// All registers that are callee-preserved (must be preserved by callee)
    pub preserved: &'static [PReg],
    /// All registers that are callee-clobbered (must be preserved by caller)
    pub clobbered: &'static [PReg],
    /// Registers that are not able to be allocated, that register should
    /// be treated as not being under the control of the register allocator.
    pub unavailable: &'static [PReg],
    /// A suggested set of "high priority" registers when a register allocator has no
    /// reason to use any other registers.
    ///
    /// These will be preferred over other registers if any are available, and it is assumed
    /// that occurring earlier in the list means higher relative priority.
    pub high_priority_temporaries: &'static [PReg],
}

/// Interface for a generic "stack frame" that a target can implement. This is used by the code generator
/// to place data in the correct place at the function level.
///
/// This is a stateful type, the code generator and register allocator are both expected
/// to use this when manipulating the stack and whatnot.
pub trait StackFrame<Arch: Architecture> {
    /// Informs the frame of a stack object that is being used. The frame returns a
    /// location that the stack object can be accessed through.
    fn stack_slot(
        &mut self,
        stack: StackSlot,
        context: FramelessCtx<'_, '_, '_, Arch>,
    ) -> VariableLocation;

    /// Emits a copy from the location of a function parameter into a vreg during instruction selection.
    fn lower_parameter(
        &mut self,
        param: Value,
        result: WriteableReg,
        context: FramelessCtx<'_, '_, '_, Arch>,
    );

    /// Lowers a return instruction, handling moving values into the correct spot according to the ABI.
    fn lower_ret(&mut self, ret: &ir::RetInst, context: FramelessCtx<'_, '_, '_, Arch>);

    /// "Spills" a register that is `bytes` bytes long, returning a stack location for it.
    ///
    /// It's up to the caller to store this location and re-use it.
    fn spill_slot(&mut self, bytes: usize) -> VariableLocation;

    /// Used to inform a frame that a "callee-preserved" register has been used directly
    /// and thus needs to be preserved.
    fn preserved_reg_used(&mut self, reg: PReg);

    /// Used to inform a frame of register use/def information for call instructions.
    ///
    /// This is called by the calling convention when a `call`-like instruction is
    /// generated, with a list of used registers and a list of defined registers.
    ///
    /// This is used later in the register allocator, this just happens to be the best place
    /// to store this information.
    fn register_use_def_call(&mut self, call: Arch::Inst, uses: &[PReg], defs: &[PReg]);

    /// Returns the use-def information previously given to [`Self::register_use_def_call`].
    fn call_use_defs(&self, call: Arch::Inst) -> (&[PReg], &[PReg]);

    /// Returns the use-def information of a `ret`-like instruction
    fn ret_uses(&self, ret: Arch::Inst) -> &[PReg];

    /// Called during the final emitting phase, will emit a function's prologue (if necessary).
    ///
    /// This relies on the fact that the frame is maintained through all backend phases,
    /// so the object will know if a prologue is necessary.
    fn generate_prologue(&self, out: &mut Vec<Arch::Inst>);

    /// Called during the final emitting phase, will emit a function's epilogue (if necessary).
    ///
    /// This relies on the fact that the frame is maintained through all backend phases,
    /// so the object will know if an epilogue is necessary.
    fn generate_epilogue(&self, out: &mut Vec<Arch::Inst>);

    /// Returns a representation of the available registers for allocation.
    fn registers(&self) -> AvailableRegisters;

    /// Gets the metadata for the associated SIR function at the time of lowering
    fn metadata(&self) -> FunctionMetadata;
}
