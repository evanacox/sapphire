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
use crate::codegen::x86_64::{
    greedy_isel, ALUOpcode, IndirectAddress, Inst, Lea, Mov, Pop, Push, RegMemImm, Ret, Width, ALU,
    X86_64,
};
use crate::codegen::{
    AvailableRegisters, CallingConv, CodegenOptions, Ctx, FramelessCtx, LoweringContext, PReg, Reg,
    StackFrame, Target, VariableLocation, WriteableReg,
};
use crate::ir;
use crate::ir::{
    Array, Cursor, FuncView, Function, FunctionMetadata, Signature, StackSlot, Struct, Type,
    TypePool, UType, Value,
};
use crate::utility::SaHashMap;
use smallvec::SmallVec;
use std::iter;

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
    metadata: FunctionMetadata,
    stack_size: usize,
    additional: usize,
    options: CodegenOptions,
    slot_distance_from_rbp: SecondaryMap<StackSlot, usize>,
    preserved_regs_used: SmallVec<[PReg; 8]>,
    signature_abi: SignatureABI,
}

macro_rules! manipulate_rsp {
    ($self:expr, $out:expr, $opc:expr) => {{
        $out.push(Inst::ALU(ALU {
            opc: $opc,
            width: Width::Qword,
            lhs: WriteableReg::from_reg(Reg::from_preg(X86_64::RSP)),
            rhs: RegMemImm::Imm($self.stack_size as i32),
        }));
    }};
}

impl SystemVStackFrame {
    pub(in crate::codegen::x86_64) fn new(func: &Function, target: &Target<X86_64>) -> Self {
        let metadata = func.compute_metadata().unwrap();
        let view = FuncView::over(func);
        let function_params = view.block_params(view.entry_block().unwrap());
        let sig = func.signature();

        let mut obj = Self {
            metadata,
            stack_size: 0,
            additional: 0,
            options: target.options(),
            slot_distance_from_rbp: SecondaryMap::default(),
            preserved_regs_used: SmallVec::default(),
            signature_abi: SignatureABI::classify(sig, function_params),
        };

        let view = FuncView::over(func);

        for slot in view.dfg().stack_slots() {
            let data = view.dfg().stack_slot(slot);
            let layout = target.layout_of(data.ty());
            let sz = layout.size() as usize;

            obj.align_stack_for(layout.align() as usize);

            // we add `layout.size()` because we're getting the address of the FIRST
            // byte, and the stack grows downwards.
            //
            // ex: 8 byte object, 0 byte stack so far.
            //     we want to start at `[rbp - 8]` not `[rbp]`, because the latter
            //     would load the return address
            //
            obj.stack_size += sz;
            obj.slot_distance_from_rbp.insert(slot, obj.stack_size);
        }

        // keep stack aligned to 8-byte boundaries at all times
        obj.stack_size += obj.stack_size % 8;

        obj
    }

    #[inline]
    fn will_omit_fp(&self) -> bool {
        !self.metadata.has_alloca && self.options.omit_frame_pointer
    }

    #[inline]
    fn align_stack_for(&mut self, align: usize) {
        debug_assert!(align.is_power_of_two());

        // if we haven't allocated anything then stack isn't properly aligned,
        // it was 16/32-byte aligned before the return address was pushed so if
        // we add 8 it will be 16-byte aligned again
        //
        // note that we don't do this if we will emit a frame pointer, because
        // the prologue would do `push rbp` and add an extra 8
        if self.stack_size == 0 && !self.metadata.is_leaf && !self.metadata.has_alloca {
            self.stack_size += 8;

            // almost every type only has <= 16-byte alignment here, once we've added
            // to get us back to 16 byte alignment we're good to go
            if align <= 16 {
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
        if self.will_omit_fp() {
            // if we omit the frame pointer, offsets are reduced by 8 because they no longer include the pushed `%rbp`.
            // we also need to include the stack size since `RSP` has been mutated
            let including_stack_size = offset + (self.stack_size as i32);

            IndirectAddress::RegOffset(Reg::from_preg(X86_64::RSP), including_stack_size - 8)
        } else {
            IndirectAddress::RegOffset(Reg::from_preg(X86_64::RBP), offset)
        }
    }

    #[inline]
    fn distance_from_bp_into_location(&self, distance: usize) -> VariableLocation {
        if self.will_omit_fp() {
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

    fn classify_type(pool: &TypePool, ty: Type, target: &Target<X86_64>) -> SystemVTypeClass {
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
        target: &Target<X86_64>,
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
        target: &Target<X86_64>,
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

impl StackFrame<X86_64> for SystemVStackFrame {
    fn stack_slot(
        &mut self,
        stack: StackSlot,
        (def, ctx): FramelessCtx<'_, '_, '_, X86_64>,
    ) -> VariableLocation {
        let distance = self.slot_distance_from_rbp[stack];

        self.distance_from_bp_into_location(distance)
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
                ctx.begin_caller_defined_fixed_interval(reg.as_preg().unwrap());

                greedy_isel::zeroing_mov(result, RegMemImm::Reg(reg), def.dfg.ty(param), ctx);

                ctx.end_caller_defined_fixed_interval(reg.as_preg().unwrap());
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

                    ctx.begin_fixed_interval(&[reg]);

                    greedy_isel::zeroing_mov(
                        WriteableReg::from_reg(Reg::from_preg(reg)),
                        RegMemImm::Reg(result),
                        ty,
                        ctx,
                    );

                    ctx.emit(Inst::Ret(Ret {}));
                    ctx.end_fixed_interval(&[reg]);
                }
                _ => todo!("aggregates that fit in registers"),
            }
        }
    }

    fn spill_slot(&mut self, bytes: usize) -> VariableLocation {
        self.align_stack_for(bytes);
        self.stack_size += bytes;

        // we give the register allocator spill locations near the bottom of the stack
        // if we omit the frame pointer, this way we make it so that the old stack offsets
        // are actually still valid.
        self.distance_from_bp_into_location(self.stack_size)
    }

    fn preserved_reg_used(&mut self, reg: PReg) {
        if !self.preserved_regs_used.contains(&reg) {
            self.preserved_regs_used.push(reg);
        }
    }

    fn register_use_def_call(&mut self, call: Inst, uses: &[PReg], defs: &[PReg]) {
        todo!()
    }

    fn call_use_defs(&self, call: Inst) -> (&[PReg], &[PReg]) {
        todo!()
    }

    fn ret_uses(&self, ret: Inst) -> &[PReg] {
        &self.signature_abi.ret
    }

    fn generate_prologue(&self, out: &mut Vec<Inst>) {
        // push any preserved registers if needed
        for &reg in self.preserved_regs_used.iter() {
            out.push(Inst::Push(Push {
                value: Reg::from_preg(reg),
                width: Width::Qword,
            }));
        }

        if !self.will_omit_fp() {
            // push rbp
            out.push(Inst::Push(Push {
                value: Reg::from_preg(X86_64::RBP),
                width: Width::Qword,
            }));

            // mov rbp, rsp
            out.push(Inst::Mov(Mov {
                src: RegMemImm::Reg(Reg::from_preg(X86_64::RSP)),
                dest: WriteableReg::from_reg(Reg::from_preg(X86_64::RBP)),
                width: Width::Qword,
            }));
        }

        if self.stack_size != 0 {
            // sub rsp, stack_size
            manipulate_rsp!(self, out, ALUOpcode::Sub);
        }
    }

    fn generate_epilogue(&self, out: &mut Vec<Inst>) {
        if self.stack_size != 0 {
            // add rsp, stack_size
            manipulate_rsp!(self, out, ALUOpcode::Add);
        }

        if !self.will_omit_fp() {
            // pop rbp
            out.push(Inst::Pop(Pop {
                dest: WriteableReg::from_reg(Reg::from_preg(X86_64::RBP)),
                width: Width::Qword,
            }));
        }

        // pop any preserved registers if needed
        for &reg in self.preserved_regs_used.iter().rev() {
            out.push(Inst::Pop(Pop {
                dest: WriteableReg::from_reg(Reg::from_preg(reg)),
                width: Width::Qword,
            }));
        }
    }

    fn registers(&self) -> AvailableRegisters {
        const CALLEE_PRESERVED: [PReg; 6] = [
            X86_64::RBX,
            X86_64::R12,
            X86_64::R13,
            X86_64::R14,
            X86_64::R15,
            X86_64::RBP,
        ];

        // rbp isn't available to allocate at all unless we're omitting the frame pointer,
        // if it isn't available to allocate then we manage rbp and don't have to tell the
        // register allocator to preserve it
        let callee_preserved = if self.will_omit_fp() {
            &CALLEE_PRESERVED[..6]
        } else {
            &CALLEE_PRESERVED[..5]
        };

        const CALLER_PRESERVED: [PReg; 9] = [
            X86_64::RAX,
            X86_64::RCX,
            X86_64::RDX,
            X86_64::RDI,
            X86_64::RSI,
            X86_64::R8,
            X86_64::R9,
            X86_64::R10,
            X86_64::R11,
        ];

        const UNAVAILABLE: [PReg; 3] = [X86_64::RIP, X86_64::RSP, X86_64::RBP];

        let un_allocatable = if self.will_omit_fp() {
            &UNAVAILABLE[0..2]
        } else {
            &UNAVAILABLE[0..3]
        };

        AvailableRegisters {
            preserved: callee_preserved,
            clobbered: &CALLER_PRESERVED,
            unavailable: un_allocatable,
            high_priority_temporaries: &[],
        }
    }

    fn metadata(&self) -> FunctionMetadata {
        self.metadata
    }
}

/// Models the System-V calling convention
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
