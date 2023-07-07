//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::{
    Architecture, CodegenOptions, FramelessCtx, LoweringContext, Reg, VariableLocation,
    WriteableReg,
};
use crate::ir;
use crate::ir::{Function, StackSlot, Value};

/// Interface for a generic "stack frame" that a target can implement. This is used by the code generator
/// to place data in the correct place at the function level.
///
/// This is a stateful type, the code generator and register allocator are both expected
/// to use this when manipulating the stack and whatnot.
pub trait StackFrame<Arch: Architecture> {
    /// Computes the stack size necessary for the function (before spills)
    fn compute_stack_layout(&mut self, func: &Function, ctx: &mut LoweringContext<'_, '_, Arch>);

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

    /// "Spills" a register, returning a stack location for it.
    fn spill(&mut self, reg: Reg, options: CodegenOptions) -> VariableLocation;

    /// Called during the final emitting phase, will emit a function's prologue (if necessary).
    ///
    /// This relies on the fact that the frame is maintained through all backend phases,
    /// so the object will know if a prologue is necessary.
    fn generate_prologue(&self, out: &mut Vec<Arch::Inst>, options: CodegenOptions);

    /// Called during the final emitting phase, will emit a function's epilogue (if necessary).
    ///
    /// This relies on the fact that the frame is maintained through all backend phases,
    /// so the object will know if an epilogue is necessary.
    fn generate_epilogue(&self, out: &mut Vec<Arch::Inst>, options: CodegenOptions);
}
