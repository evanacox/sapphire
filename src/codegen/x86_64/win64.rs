//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::x86_64::{Inst, X86_64};
use crate::codegen::{
    AvailableRegisters, CallUseDef, CallUseDefId, CallingConv, Ctx, FramelessCtx, PReg, StackFrame,
    VariableLocation, WriteableReg,
};
use crate::ir;
use crate::ir::{FunctionMetadata, Signature, StackSlot, Value};

/// An implementation of [`StackFrame`] for the Windows x64 ABI.
///
/// This ABI is for x86-64 on the Windows operating system.
pub struct WindowsX64StackFrame;

/// An implementation of [`CallingConv`] for the Windows x64 ABI.
///
/// This ABI is for x86-64 on the Windows operating system.
pub struct WindowsX64CallingConv;

impl WindowsX64CallingConv {
    pub(in crate::codegen::x86_64) fn new(
        sig: &Signature,
        function_params: &[Value],
        metadata: FunctionMetadata,
    ) -> Self {
        todo!()
    }
}

impl StackFrame<X86_64> for WindowsX64StackFrame {
    fn stack_slot(
        &mut self,
        stack: StackSlot,
        context: FramelessCtx<'_, '_, '_, X86_64>,
    ) -> VariableLocation {
        todo!()
    }

    fn lower_parameter(
        &mut self,
        param: Value,
        result: WriteableReg,
        context: FramelessCtx<'_, '_, '_, X86_64>,
    ) {
        todo!()
    }

    fn lower_ret(&mut self, ret: &ir::RetInst, context: FramelessCtx<'_, '_, '_, X86_64>) {
        todo!()
    }

    fn spill_slot(&mut self, size: usize) -> VariableLocation {
        todo!()
    }

    fn preserved_reg_used(&mut self, reg: PReg) {
        todo!()
    }

    fn register_use_def_call(&mut self, use_def: CallUseDef<'_>) -> CallUseDefId {
        todo!()
    }

    fn call_use_defs(&self, id: CallUseDefId) -> CallUseDef<'_> {
        todo!()
    }

    fn ret_uses(&self) -> &[PReg] {
        todo!()
    }

    fn generate_prologue(&self, out: &mut Vec<Inst>) {
        todo!()
    }

    fn generate_epilogue(&self, out: &mut Vec<Inst>) {
        todo!()
    }

    fn registers(&self) -> AvailableRegisters {
        todo!()
    }

    fn metadata(&self) -> FunctionMetadata {
        todo!()
    }

    fn stack_size(&self) -> usize {
        todo!()
    }
}

impl CallingConv<X86_64> for WindowsX64CallingConv {
    fn lower_call(
        &self,
        call: &ir::CallInst,
        result: Option<WriteableReg>,
        context: Ctx<'_, '_, '_, '_, X86_64>,
    ) {
        todo!()
    }

    fn lower_indirect_call(
        &self,
        call: &ir::IndirectCallInst,
        result: Option<WriteableReg>,
        context: Ctx<'_, '_, '_, '_, X86_64>,
    ) {
        todo!()
    }
}
