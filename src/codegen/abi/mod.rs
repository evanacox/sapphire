//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

mod aggregates;
mod calling_conv;
mod frame;
mod layout;

use crate::codegen::{
    Architecture, CodegenOptions, Ctx, FramelessCtx, LoweringContext, MachInst, PReg, Reg, Target,
    TypeLayout, WriteableReg,
};
use crate::ir;
use crate::ir::{
    Function, FunctionDefinition, FunctionMetadata, Signature, StackSlot, Type, TypePool, Value,
};
pub use aggregates::*;
pub use layout::*;

/// Details about a specific target ABI necessary for code generation.
pub trait ABI<Arch: Architecture, Inst: MachInst<Arch>>: Sized {
    /// Models the stack frame, calling convention info, and other ABI responsibilities for a function.
    type Frame: FunctionFrame<Arch, Self, Inst>;

    /// Returns a list of all the registers that must be preserved by the **caller** of
    /// a function. These are also known as "volatile" registers in some ABIs.
    ///
    /// If a function calls another and needs to maintain values in these registers,
    /// they must be preserved somehow.
    fn callee_preserved() -> &'static [PReg];

    /// Returns a list of all the registers that are preserved by the **callee**
    /// of a function. These are known as "non-volatile" registers in some ABIs.
    ///
    /// If a function needs to modify these, they must preserve
    /// their values first and restore them before returning.
    fn caller_preserved() -> &'static [PReg];

    /// Gets the frame pointer register for the ABI
    fn frame_pointer() -> PReg;

    /// Gets the `sp` register for the ABI
    fn stack_pointer() -> PReg;

    /// Returns the required stack alignment for a function call to be performed.
    fn stack_alignment() -> u64;

    /// Gets a new frame for the current function
    #[inline]
    fn new_frame(
        sig: &Signature,
        function_params: &[Value],
        metadata: FunctionMetadata,
    ) -> Self::Frame {
        <Self::Frame as FunctionFrame<Arch, Self, Inst>>::new(sig, function_params, metadata)
    }

    /// Checks if a type can be passed in registers or not.
    fn can_pass_in_registers(pool: &TypePool, ty: Type, layout: TypeLayout) -> bool;
}

/// The location of a single "variable." This denotes something at the ABI level,
/// e.g. `stackslot`s, parameters and the like. This identifies where they are
/// in a way that the code generator can understand.
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

/// Interface for a generic "stack frame" that a target can implement. This is used by the code generator
/// to place data in the correct place at the function level.
///
/// This is a stateful type, the code generator and register allocator are both expected
/// to use this when manipulating the stack and whatnot.
pub trait FunctionFrame<Arch: Architecture, Abi: ABI<Arch, Inst>, Inst: MachInst<Arch>> {
    /// Creates a new stack frame with nothing in it.
    ///
    /// `function_params` must be the block parameters for the entry block
    /// of the SIR function this frame is for, and `metadata` must be the result of
    /// [`Function::compute_metadata`](ir::Function::compute_metadata) for the function
    /// the frame is for.
    fn new(sig: &Signature, function_params: &[Value], metadata: FunctionMetadata) -> Self;

    /// Computes the stack size necessary for the function (before spills)
    fn compute_stack_layout(
        &mut self,
        func: &Function,
        ctx: &mut LoweringContext<'_, '_, Arch, Abi, Inst>,
    );

    /// Informs the frame of a stack object that is being used. The frame returns a
    /// location that the stack object can be accessed through.
    fn stack_slot(
        &mut self,
        stack: StackSlot,
        context: FramelessCtx<'_, '_, '_, Arch, Abi, Inst>,
    ) -> VariableLocation;

    /// Emits a copy from the location of a function parameter into a vreg during instruction selection.
    fn lower_parameter(
        &mut self,
        param: Value,
        result: WriteableReg,
        context: FramelessCtx<'_, '_, '_, Arch, Abi, Inst>,
    );

    /// Lowers a call instruction, handling passing arguments according to ABI rules. If
    /// the call returns a result, the result is stored into the register in `result`.
    fn lower_call(
        &mut self,
        call: &ir::CallInst,
        result: Option<WriteableReg>,
        context: FramelessCtx<'_, '_, '_, Arch, Abi, Inst>,
    );

    /// Lowers an indirect call instruction, handling passing arguments according to ABI rules. If
    /// the call returns a result, the result is stored into the register in `result`.
    fn lower_indirect_call(
        &mut self,
        call: &ir::IndirectCallInst,
        result: Option<WriteableReg>,
        context: FramelessCtx<'_, '_, '_, Arch, Abi, Inst>,
    );

    /// Lowers a return instruction, handling moving values into the correct spot according to the ABI.
    fn lower_ret(&mut self, ret: &ir::RetInst, context: FramelessCtx<'_, '_, '_, Arch, Abi, Inst>);

    /// "Spills" a register, returning a stack location for it.
    fn spill(&mut self, reg: Reg, options: CodegenOptions) -> VariableLocation;

    /// Called during the final emitting phase, will emit a function's prologue (if necessary).
    ///
    /// This relies on the fact that the frame is maintained through all backend phases,
    /// so the object will know if a prologue is necessary.
    fn generate_prologue(&self, out: &mut Vec<Inst>, options: CodegenOptions);

    /// Called during the final emitting phase, will emit a function's epilogue (if necessary).
    ///
    /// This relies on the fact that the frame is maintained through all backend phases,
    /// so the object will know if an epilogue is necessary.
    fn generate_epilogue(&self, out: &mut Vec<Inst>, options: CodegenOptions);
}
