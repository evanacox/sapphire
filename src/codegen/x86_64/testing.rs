//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::x86_64::{Inst, SystemVStackFrame, X86_64};
use crate::codegen::{
    AvailableRegisters, CallUseDef, CallUseDefId, FramelessCtx, PReg, StackFrame, VariableLocation,
    WriteableReg,
};
use crate::ir::{FunctionMetadata, RetInst, StackSlot, Value};

/// A debug stack frame setup that only makes 3 registers available for
/// the register allocator.
pub struct Debug3RegStackFrame {
    frame: SystemVStackFrame,
}

impl Debug3RegStackFrame {
    /// Creates a new debug stack frame that wraps `frame`]
    pub fn wrap(frame: SystemVStackFrame) -> Self {
        Self { frame }
    }
}

impl StackFrame<X86_64> for Debug3RegStackFrame {
    fn stack_slot(
        &mut self,
        stack: StackSlot,
        context: FramelessCtx<'_, '_, '_, X86_64>,
    ) -> VariableLocation {
        self.frame.stack_slot(stack, context)
    }

    fn lower_parameter(
        &mut self,
        param: Value,
        result: WriteableReg,
        context: FramelessCtx<'_, '_, '_, X86_64>,
    ) {
        self.frame.lower_parameter(param, result, context)
    }

    fn lower_ret(&mut self, ret: &RetInst, context: FramelessCtx<'_, '_, '_, X86_64>) {
        self.frame.lower_ret(ret, context)
    }

    fn spill_slot(&mut self, bytes: usize) -> VariableLocation {
        self.frame.spill_slot(bytes)
    }

    fn preserved_reg_used(&mut self, reg: PReg) {
        self.frame.preserved_reg_used(reg)
    }

    fn register_use_def_call(&mut self, use_def: CallUseDef<'_>) -> CallUseDefId {
        self.frame.register_use_def_call(use_def)
    }

    fn call_use_defs(&self, id: CallUseDefId) -> CallUseDef<'_> {
        self.frame.call_use_defs(id)
    }

    fn ret_uses(&self) -> &[PReg] {
        self.frame.ret_uses()
    }

    fn generate_prologue(&self, out: &mut Vec<Inst>) {
        self.frame.generate_prologue(out)
    }

    fn generate_epilogue(&self, out: &mut Vec<Inst>) {
        self.frame.generate_epilogue(out)
    }

    fn registers(&self) -> AvailableRegisters {
        const CLOBBERED_FLOATS: [PReg; 3] = [X86_64::xmm(8), X86_64::xmm(9), X86_64::xmm(10)];

        AvailableRegisters {
            preserved: (&[], &[]),
            clobbered: (&[X86_64::R8, X86_64::R9, X86_64::R10], &CLOBBERED_FLOATS),
            unavailable: (&[X86_64::RIP, X86_64::RSP, X86_64::RBP], &[]),
            high_priority_temporaries: (&[], &[]),
        }
    }

    fn metadata(&self) -> FunctionMetadata {
        self.frame.metadata()
    }

    fn stack_size(&self) -> usize {
        self.frame.stack_size()
    }
}
