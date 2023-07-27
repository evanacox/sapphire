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
    AvailableRegisters, CallUseDefId, FramelessCtx, PReg, StackFrame, VariableLocation,
    WriteableReg,
};
use crate::ir::{FunctionMetadata, RetInst, StackSlot, Value};

/// A debug stack frame setup that only makes 2 registers available for
/// the register allocator.
pub struct Debug2RegStackFrame {
    frame: SystemVStackFrame,
}

impl StackFrame<X86_64> for Debug2RegStackFrame {
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

    fn register_use_def_call(&mut self, uses: &[PReg], defs: &[PReg]) -> CallUseDefId {
        self.frame.register_use_def_call(uses, defs)
    }

    fn call_use_defs(&self, id: CallUseDefId) -> (&[PReg], &[PReg]) {
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
        AvailableRegisters {
            preserved: &[],
            clobbered: &[X86_64::R10, X86_64::R11],
            unavailable: &[],
            high_priority_temporaries: &[],
        }
    }

    fn metadata(&self) -> FunctionMetadata {
        self.frame.metadata()
    }

    fn stack_size(&self) -> usize {
        self.frame.stack_size()
    }
}
