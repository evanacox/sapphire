//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::{Architecture, CallingConv, PReg, Reg, StackFrame, TypeLayout};
use crate::ir::{Type, TypePool};

/// Details about a specific target ABI necessary for code generation.
pub trait ABI<Arch: Architecture>: Sized {
    /// The associated stack frame type for this ABI
    type Frame: StackFrame<Arch>;

    /// The associated calling convention type for this ABI
    type CallingConv: CallingConv<Arch>;

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
