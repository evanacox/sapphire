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
use crate::codegen::x86_64::{greedy_isel, IndirectAddress, Lea, Ret};
use crate::codegen::x86_64::{Inst, Mov, RegMemImm, X86_64};
use crate::codegen::{
    CodegenOptions, Ctx, FramelessCtx, FunctionFrame, LoweringContext, PReg, Reg, Target,
    TypeLayout, VariableLocation, WriteableReg, ABI,
};
use crate::ir::{
    Array, CallInst, Cursor, FuncView, Function, FunctionDefinition, FunctionMetadata,
    IndirectCallInst, InstData, RetInst, Signature, StackSlot, Struct, Type, TypePool, UType,
    Value,
};
use crate::utility::SaHashMap;
use smallvec::SmallVec;
use std::iter;

/// The x86-64 System V ABI.
///
/// This is the dominant ABI for Linux, macOS, BSDs and other *nix platforms
/// on the x86-64 platform.
pub struct SystemV;

#[allow(clippy::upper_case_acronyms)]
#[repr(u8)]
#[derive(Copy, Clone)]
enum SystemVTypeClass {
    Integer,
    SSE,
    SSEUp,
    X87,
    X87Up,
    ComplexX87,
    Memory,
    NoClass,
}

impl SystemV {
    fn classify_type(
        pool: &TypePool,
        ty: Type,
        target: &Target<X86_64, SystemV, Inst>,
    ) -> SystemVTypeClass {
        match ty.unpack() {
            UType::Int(_) | UType::Bool(_) | UType::Ptr(_) => SystemVTypeClass::Integer,
            UType::Float(_) => SystemVTypeClass::SSE,
            UType::Struct(structure) => Self::classify_struct(pool, ty, structure, target),
            UType::Array(array) => Self::classify_array(pool, ty, array, target),
        }
    }

    fn classify_array(
        pool: &TypePool,
        ty: Type,
        array: Array,
        target: &Target<X86_64, SystemV, Inst>,
    ) -> SystemVTypeClass {
        let layout = target.layout_of(ty);

        if layout.size() > 64 {
            return SystemVTypeClass::Memory;
        }

        todo!()
    }

    fn classify_struct(
        pool: &TypePool,
        ty: Type,
        structure: Struct,
        target: &Target<X86_64, SystemV, Inst>,
    ) -> SystemVTypeClass {
        let layout = target.layout_of(ty);

        if layout.size() > 64 {
            return SystemVTypeClass::Memory;
        }

        //
        // possible algo:
        //
        // set up an array of bytes, each byte with classification
        // deal with 8 at a time
        //
        //

        let members = structure.members(pool);

        // initialize our list of eight-bytes to NO_CLASS
        let words = SmallVec::<[SystemVTypeClass; 16]>::from_iter(
            iter::repeat(SystemVTypeClass::NoClass).take(layout.size() as usize),
        );

        for i in 0..(members.len() - 1) {}

        todo!()
    }
}

impl ABI<X86_64, Inst> for SystemV {
    type Frame = SystemVFrame;

    fn callee_preserved() -> &'static [PReg] {
        todo!()
    }

    fn caller_preserved() -> &'static [PReg] {
        todo!()
    }

    fn frame_pointer() -> PReg {
        todo!()
    }

    fn stack_pointer() -> PReg {
        todo!()
    }

    fn stack_alignment() -> u64 {
        todo!()
    }

    fn can_pass_in_registers(pool: &TypePool, ty: Type, layout: TypeLayout) -> bool {
        todo!()
    }
}

/// The x64 Windows ABI
///
/// This is the dominant ABI for x86-64 on Windows.
pub struct WindowsX64;

impl ABI<X86_64, Inst> for WindowsX64 {
    type Frame = WindowsX64Frame;

    fn callee_preserved() -> &'static [PReg] {
        todo!()
    }

    fn caller_preserved() -> &'static [PReg] {
        todo!()
    }

    fn frame_pointer() -> PReg {
        todo!()
    }

    fn stack_pointer() -> PReg {
        todo!()
    }

    fn stack_alignment() -> u64 {
        todo!()
    }

    fn can_pass_in_registers(pool: &TypePool, ty: Type, layout: TypeLayout) -> bool {
        todo!()
    }
}

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

/// An implementation of [`FunctionFrame`] for the System-V ABI.
///
/// This ABI is for x86-64 on most Unix platforms (Linux, macOS, BSD).
pub struct SystemVFrame {
    able_to_omit: bool,
    is_leaf: bool,
    stack_size: usize,
    additional: usize,
    slot_distance_from_rbp: SecondaryMap<StackSlot, usize>,
    param_locations: SaHashMap<Value, ParamLocation>,
}

impl SystemVFrame {
    #[inline]
    fn will_omit_fp(&self, ctx: &LoweringContext<'_, '_, X86_64, SystemV, Inst>) -> bool {
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
        ctx: &mut LoweringContext<'_, '_, X86_64, SystemV, Inst>,
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

impl FunctionFrame<X86_64, SystemV, Inst> for SystemVFrame {
    fn new(sig: &Signature, function_params: &[Value], metadata: FunctionMetadata) -> Self {
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
        for (&(param, attributes), &val) in sig.params().iter().zip(function_params.iter()) {
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

        Self {
            able_to_omit: !metadata.has_alloca,
            is_leaf: metadata.is_leaf,
            stack_size: 0,
            additional: 0,
            slot_distance_from_rbp: SecondaryMap::default(),
            param_locations: locations,
        }
    }

    fn compute_stack_layout(
        &mut self,
        func: &Function,
        ctx: &mut LoweringContext<'_, '_, X86_64, SystemV, Inst>,
    ) {
        let mut view = FuncView::over(func);

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
        (def, ctx): FramelessCtx<'_, '_, '_, X86_64, SystemV, Inst>,
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
        (def, ctx): FramelessCtx<'_, '_, '_, X86_64, SystemV, Inst>,
    ) {
        match self
            .param_locations
            .get(&param)
            .expect("value is not a parameter")
        {
            ParamLocation::InReg(reg) => {
                greedy_isel::zeroing_mov(result, RegMemImm::Reg(*reg), def.dfg.ty(param), ctx);
            }
            ParamLocation::RelativeToFP(offset) => {
                let loc = self.fp_relative_offset_into_indirect_address(*offset, ctx);

                greedy_isel::zeroing_mov(result, RegMemImm::Mem(loc), def.dfg.ty(param), ctx);
            }
            ParamLocation::LeaFromFP(offset) => {
                let loc = self.fp_relative_offset_into_indirect_address(*offset, ctx);

                ctx.emit(Inst::Lea(Lea {
                    dest: result,
                    src: loc,
                }))
            }
        }
    }

    fn lower_call(
        &mut self,
        call: &CallInst,
        result: Option<WriteableReg>,
        context: FramelessCtx<'_, '_, '_, X86_64, SystemV, Inst>,
    ) {
        todo!()
    }

    fn lower_indirect_call(
        &mut self,
        call: &IndirectCallInst,
        result: Option<WriteableReg>,
        context: FramelessCtx<'_, '_, '_, X86_64, SystemV, Inst>,
    ) {
        todo!()
    }

    fn lower_ret(
        &mut self,
        ret: &RetInst,
        (def, ctx): FramelessCtx<'_, '_, '_, X86_64, SystemV, Inst>,
    ) {
        if let Some(val) = ret.value() {
            let ty = def.dfg.ty(val);
            let out = match ty.unpack() {
                UType::Float(f) => X86_64::xmm(0),
                UType::Int(_) | UType::Bool(_) | UType::Ptr(_) => X86_64::RAX,
                _ => todo!("aggregates that fit in registers"),
            };

            let result = ctx.result_reg(val, out.class());

            greedy_isel::zeroing_mov(
                WriteableReg::from_reg(Reg::from_preg(out)),
                RegMemImm::Reg(result),
                ty,
                ctx,
            );
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

/// An implementation of [`FunctionFrame`] for the Windows x64 ABI.
///
/// This ABI is for x86-64 on the Windows operating system.
pub struct WindowsX64Frame;

impl FunctionFrame<X86_64, WindowsX64, Inst> for WindowsX64Frame {
    fn new(sig: &Signature, function_params: &[Value], metadata: FunctionMetadata) -> Self {
        todo!()
    }

    fn compute_stack_layout(
        &mut self,
        func: &Function,
        ctx: &mut LoweringContext<'_, '_, X86_64, WindowsX64, Inst>,
    ) {
        todo!()
    }

    fn stack_slot(
        &mut self,
        stack: StackSlot,
        context: FramelessCtx<'_, '_, '_, X86_64, WindowsX64, Inst>,
    ) -> VariableLocation {
        todo!()
    }

    fn lower_parameter(
        &mut self,
        param: Value,
        result: WriteableReg,
        context: FramelessCtx<'_, '_, '_, X86_64, WindowsX64, Inst>,
    ) {
        todo!()
    }

    fn lower_call(
        &mut self,
        call: &CallInst,
        result: Option<WriteableReg>,
        context: FramelessCtx<'_, '_, '_, X86_64, WindowsX64, Inst>,
    ) {
        todo!()
    }

    fn lower_indirect_call(
        &mut self,
        call: &IndirectCallInst,
        result: Option<WriteableReg>,
        context: FramelessCtx<'_, '_, '_, X86_64, WindowsX64, Inst>,
    ) {
        todo!()
    }

    fn lower_ret(
        &mut self,
        ret: &RetInst,
        context: FramelessCtx<'_, '_, '_, X86_64, WindowsX64, Inst>,
    ) {
        todo!()
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
