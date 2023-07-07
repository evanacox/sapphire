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
use crate::codegen::x86_64::{greedy_isel, IndirectAddress, Inst, Lea, RegMemImm, Ret, X86_64};
use crate::codegen::{
    CallingConv, CodegenOptions, Ctx, FramelessCtx, LoweringContext, PReg, Reg, StackFrame,
    TypeLayout, VariableLocation, WriteableReg,
};
use crate::ir;
use crate::ir::{Cursor, FuncView, Function, FunctionMetadata, Signature, StackSlot, UType, Value};
use crate::utility::SaHashMap;
use smallvec::SmallVec;

#[derive(Copy, Clone)]
enum ParamLocation {
    /// Says that a variable is located in a register
    InReg(Reg),
    /// Says that a variable is located at an offset relative to the frame pointer after
    /// the canonical prologue has executed.
    RelativeToFP(i32),
    /// Says that a variable can be calculated with `lea ..., [rbp + offset]`. This is
    /// for `byval(<n>)` pointer parameters where the address itself may be observed.
    LeaFromFP(i32),
}

struct SignatureABI {
    params: SaHashMap<Value, ParamLocation>,
    ret: SmallVec<[PReg; 2]>,
}

impl SignatureABI {
    fn classify(sig: &Signature, params: &[Value]) -> Self {
        const INTEGER_PARAM_REGISTERS: [PReg; 6] = [
            X86_64::RDI,
            X86_64::RSI,
            X86_64::RDX,
            X86_64::RCX,
            X86_64::R8,
            X86_64::R9,
        ];

        const FLOAT_PARAM_REGISTERS: [PReg; 8] = [
            X86_64::xmm(0),
            X86_64::xmm(1),
            X86_64::xmm(2),
            X86_64::xmm(3),
            X86_64::xmm(4),
            X86_64::xmm(5),
            X86_64::xmm(6),
            X86_64::xmm(7),
        ];

        let mut next_int_reg = INTEGER_PARAM_REGISTERS.iter().copied();
        let mut next_float_reg = FLOAT_PARAM_REGISTERS.iter().copied();
        let mut locations = SaHashMap::default();
        let mut n_mem_eight_bytes = 0;

        // as usual, this assumes that there are no aggregates. The aggregate lowering pass
        // must be run before we can actually do anything with frames.
        for (&(param, attributes), &val) in sig.params().iter().zip(params.iter()) {
            // if it's a `byval(<n>)` pointer, we compute the address
            if let Some(n) = attributes.byval_size() {
                locations.insert(val, ParamLocation::LeaFromFP(8 * n_mem_eight_bytes + 16));
                n_mem_eight_bytes += (n / 8) as i32;

                continue;
            }

            // arguments are rounded up to the nearest 8 bytes (SysV 3.2.3), so we don't actually
            // need to do anything with the type width. we just see if we have any more available
            // registers for that specific argument class

            let reg = if param.is_float() {
                next_float_reg.next()
            } else {
                next_int_reg.next()
            };

            // if we don't, we just mark it as being relative to
            match reg {
                Some(reg) => {
                    locations.insert(val, ParamLocation::InReg(Reg::from_preg(reg)));
                }
                None => {
                    // at the moment control flows to our function, stack is laid out like this:
                    //   0(%rsp) => return address
                    //   8(%rsp) => first memory argument
                    //
                    // if we do our `push rbp` / `mov rbp, rsp`, this increases our offsets by 8 bytes
                    // due to pushing rbp, and everything becomes relative to %rbp instead.
                    //
                    // therefore, 8n + 16(%rbp) is the canonical way to access arguments
                    locations.insert(val, ParamLocation::RelativeToFP(8 * n_mem_eight_bytes + 16));
                    n_mem_eight_bytes += 1;
                }
            }
        }

        let mut ret = SmallVec::default();

        if let Some(ty) = sig.return_ty() {
            match ty.unpack() {
                UType::Float(f) => ret.push(X86_64::xmm(0)),
                UType::Int(_) | UType::Bool(_) | UType::Ptr(_) => ret.push(X86_64::RAX),
                _ => todo!("aggregates that fit in registers"),
            }
        }

        Self {
            params: locations,
            ret,
        }
    }
}

/// An implementation of [`StackFrame`] for the System-V ABI.
///
/// This ABI is for x86-64 on most Unix platforms (Linux, macOS, BSD).
pub struct SystemVStackFrame {
    able_to_omit: bool,
    is_leaf: bool,
    stack_size: usize,
    additional: usize,
    slot_distance_from_rbp: SecondaryMap<StackSlot, usize>,
    signature_abi: SignatureABI,
}

impl SystemVStackFrame {
    #[inline]
    fn will_omit_fp(&self, ctx: &LoweringContext<'_, '_, X86_64>) -> bool {
        self.able_to_omit && ctx.options.omit_frame_pointer
    }

    #[inline]
    fn align_stack_for(&mut self, layout: TypeLayout) {
        let align = layout.align() as usize;
        debug_assert!(align.is_power_of_two());

        // if we haven't allocated anything then stack isn't properly aligned,
        // it was 16/32-byte aligned before the return address was pushed so if
        // we add 8 it will be 16-byte aligned again
        //
        // note that we don't do this if we will emit a frame pointer, because
        // the prologue would do `push rbp` and add an extra 8
        if self.stack_size == 0 && !self.is_leaf && self.able_to_omit {
            self.stack_size += 8;

            // almost every type only has <= 16-byte alignment here, once we've added
            // to get us back to 16 byte alignment we're good to go
            if layout.align() <= 16 {
                return;
            }
        }

        // align our stack by adding the remainder between the size and `alignof(T)`
        self.stack_size += self.stack_size & (align - 1);
    }

    #[inline]
    fn fp_relative_offset_into_indirect_address(
        &self,
        offset: i32,
        ctx: &mut LoweringContext<'_, '_, X86_64>,
    ) -> IndirectAddress {
        if self.will_omit_fp(ctx) {
            // if we omit the frame pointer, offsets are reduced by 8 because they no longer include the pushed `%rbp`.
            // we also need to include the stack size since `RSP` has been mutated
            let including_stack_size = offset + (self.stack_size as i32);

            IndirectAddress::RegOffset(Reg::from_preg(X86_64::RSP), including_stack_size - 8)
        } else {
            IndirectAddress::RegOffset(Reg::from_preg(X86_64::RBP), offset)
        }
    }
}

impl SystemVStackFrame {
    pub(in crate::codegen::x86_64) fn new(
        sig: &Signature,
        function_params: &[Value],
        metadata: FunctionMetadata,
    ) -> Self {
        Self {
            able_to_omit: !metadata.has_alloca,
            is_leaf: metadata.is_leaf,
            stack_size: 0,
            additional: 0,
            slot_distance_from_rbp: SecondaryMap::default(),
            signature_abi: SignatureABI::classify(sig, function_params),
        }
    }
}

impl StackFrame<X86_64> for SystemVStackFrame {
    fn compute_stack_layout(&mut self, func: &Function, ctx: &mut LoweringContext<'_, '_, X86_64>) {
        let view = FuncView::over(func);

        for slot in view.dfg().stack_slots() {
            let data = view.dfg().stack_slot(slot);
            let layout = ctx.target.layout_of(data.ty());
            let sz = layout.size() as usize;

            self.align_stack_for(layout);

            // we add `layout.size()` because we're getting the address of the FIRST
            // byte, and the stack grows downwards.
            //
            // ex: 8 byte object, 0 byte stack so far.
            //     we want to start at `[rbp - 8]` not `[rbp]`, because the latter
            //     would load the return address
            //
            self.stack_size += sz;
            self.slot_distance_from_rbp.insert(slot, self.stack_size);
        }

        // keep stack aligned to 8-byte boundaries at all times
        self.stack_size += self.stack_size % 8;
    }

    fn stack_slot(
        &mut self,
        stack: StackSlot,
        (def, ctx): FramelessCtx<'_, '_, '_, X86_64>,
    ) -> VariableLocation {
        let distance = self.slot_distance_from_rbp[stack];

        if self.will_omit_fp(ctx) {
            // if relative to rsp we need to add since the stack grows upwards
            VariableLocation::RelativeToSP(
                i32::try_from(self.stack_size - distance).expect("stack offset exceeds i32 limit"),
            )
        } else {
            // if relative to rbp we need to subtract since the stack grows downwards
            VariableLocation::RelativeToFP(
                -i32::try_from(distance).expect("stack offset exceeds i32 limit"),
            )
        }
    }

    fn lower_parameter(
        &mut self,
        param: Value,
        result: WriteableReg,
        (def, ctx): FramelessCtx<'_, '_, '_, X86_64>,
    ) {
        match self
            .signature_abi
            .params
            .get(&param)
            .copied()
            .expect("value is not a parameter")
        {
            ParamLocation::InReg(reg) => {
                greedy_isel::zeroing_mov(result, RegMemImm::Reg(reg), def.dfg.ty(param), ctx);
            }
            ParamLocation::RelativeToFP(offset) => {
                let loc = self.fp_relative_offset_into_indirect_address(offset, ctx);

                greedy_isel::zeroing_mov(result, RegMemImm::Mem(loc), def.dfg.ty(param), ctx);
            }
            ParamLocation::LeaFromFP(offset) => {
                let loc = self.fp_relative_offset_into_indirect_address(offset, ctx);

                ctx.emit(Inst::Lea(Lea {
                    dest: result,
                    src: loc,
                }))
            }
        }
    }

    fn lower_ret(&mut self, ret: &ir::RetInst, (def, ctx): FramelessCtx<'_, '_, '_, X86_64>) {
        if let Some(val) = ret.value() {
            let ty = def.dfg.ty(val);

            match ty.unpack() {
                UType::Float(_) | UType::Int(_) | UType::Bool(_) | UType::Ptr(_) => {
                    let reg = self.signature_abi.ret[0];
                    let result = ctx.result_reg(val, reg.class());

                    greedy_isel::zeroing_mov(
                        WriteableReg::from_reg(Reg::from_preg(reg)),
                        RegMemImm::Reg(result),
                        ty,
                        ctx,
                    );
                }
                _ => todo!("aggregates that fit in registers"),
            }
        }

        ctx.emit(Inst::Ret(Ret {}));
    }

    fn spill(&mut self, reg: Reg, options: CodegenOptions) -> VariableLocation {
        todo!()
    }

    fn generate_prologue(&self, out: &mut Vec<Inst>, options: CodegenOptions) {
        todo!()
    }

    fn generate_epilogue(&self, out: &mut Vec<Inst>, options: CodegenOptions) {
        todo!()
    }
}

pub struct SystemVCallingConv;

impl CallingConv<X86_64> for SystemVCallingConv {
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
