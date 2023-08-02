//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::isel::{InstructionSelector, LoweringContext};
use crate::codegen::patterns::*;
use crate::codegen::x86_64::{Inst, *};
use crate::codegen::*;
use crate::ir;
use crate::ir::*;
use crate::utility::Packable;
use std::cell::RefCell;
use std::iter;

/// An instruction selector for x86-64.
///
/// This selector uses the greedy "maximal munch" principle for matching
/// instruction patterns. This may be slower than other selectors that pick
/// the first valid instruction pattern.
pub struct GreedyISel {
    current: ir::Inst,
}

macro_rules! pat {
    ($val:expr, $base:expr, $def:expr, $ctx:expr, $matcher:expr) => {
        merge_if_matches_operand($val, $base, ($def, $ctx), $matcher)
    };

    ($base:expr, $def:expr, $ctx:expr, $matcher:expr) => {
        merge_if_matches($base, ($def, $ctx), $matcher)
    };
}

macro_rules! cast {
    ($val:expr, $def:expr, $pat:path) => {
        match $def.dfg.inst_data($def.dfg.value_to_inst($val).unwrap()) {
            $pat(inner) => inner,
            _ => unreachable!(),
        }
    };
}

type Ctx<'module, 'frame, 'target, 'ctx> =
    crate::codegen::Ctx<'module, 'frame, 'target, 'ctx, X86_64>;

fn value_into_width(val: Value, (def, _, ctx): Ctx<'_, '_, '_, '_>) -> Width {
    type_into_width(def.dfg.ty(val), ctx)
}

fn type_into_width(ty: Type, ctx: &mut LoweringContext<'_, '_, X86_64>) -> Width {
    let size = ctx.target.layout_of(ty);

    Width::from_bytes(size.size() as usize)
}

fn width_dword_minimum(width: Width) -> Width {
    match width {
        Width::Byte | Width::Word => Width::Dword,
        x => x,
    }
}

fn calling_conv(
    cc: CallConv,
    ctx: &LoweringContext<'_, '_, X86_64>,
) -> &'static dyn CallingConv<X86_64> {
    match cc {
        CallConv::C => ctx.target.new_callcc(),
        CallConv::SysV => &SYS_V_CC,
        CallConv::Win64 => &WINDOWS_X64_CC,
    }
}

fn icmp_into_cc(op: ICmpOp) -> ConditionCode {
    match op {
        ICmpOp::EQ => ConditionCode::E,
        ICmpOp::NE => ConditionCode::NE,
        ICmpOp::SGT => ConditionCode::G,
        ICmpOp::SLT => ConditionCode::L,
        ICmpOp::SGE => ConditionCode::GE,
        ICmpOp::SLE => ConditionCode::LE,
        ICmpOp::UGT => ConditionCode::A,
        ICmpOp::ULT => ConditionCode::B,
        ICmpOp::UGE => ConditionCode::AE,
        ICmpOp::ULE => ConditionCode::BE,
    }
}

#[inline]
pub(in crate::codegen::x86_64) fn zeroing_mov(
    dest: WriteableReg,
    src: RegMemImm,
    ty: Type,
    ctx: &mut LoweringContext<'_, '_, X86_64>,
) {
    let width = width_dword_minimum(type_into_width(ty, ctx));

    // we emit it as a `mov` for dwords so that the entire register is cleared
    ctx.emit(Inst::Mov(Mov { width, src, dest }));
}

#[inline]
pub(in crate::codegen::x86_64) fn val_class(val: Value, def: &FunctionDefinition) -> RegClass {
    match def.dfg.ty(val).unpack() {
        UType::Float(_) => RegClass::Float,
        UType::Int(_) | UType::Bool(_) | UType::Ptr(_) => RegClass::Int,
        UType::Array(_) | UType::Struct(_) => {
            panic!("unable to put array or structure in physical register")
        }
    }
}

impl<'module, 'target, 'ctx> GreedyISel
where
    'module: 'ctx,
    'target: 'ctx,
{
    // holds all the different **pointer** patterns, e.g. `offset(stackslot(), 4)`
    #[inline]
    fn internal_rhs_pointer(
        &self,
        rhs: Value,
        (def, fr, ctx): Ctx<'_, '_, '_, '_>,
    ) -> Option<IndirectAddress> {
        // TODO

        None
    }

    // holds all the different right-hand side patterns
    #[inline]
    fn internal_rhs_immediate(
        &self,
        rhs: Value,
        (def, fr, ctx): Ctx<'_, '_, '_, '_>,
    ) -> Option<i32> {
        let base = self.current;
        let val = RefCell::new(0);

        // any imm8/imm32 we immediately fold
        if pat!(rhs, base, def, ctx, imm32(&val)) {
            return Some(*val.borrow());
        }

        None
    }

    // performs right-hand operand folding for indirect addressing, this is
    // specifically for `load`/`store` instructions trying to fold their source/dest
    fn rhs_pointer_indirect_address(
        &self,
        rhs: Value,
        (def, fr, ctx): Ctx<'_, '_, '_, '_>,
    ) -> IndirectAddress {
        match self.internal_rhs_pointer(rhs, (def, fr, ctx)) {
            Some(address) => address,
            None => IndirectAddress::Reg(ctx.result_reg(rhs, RegClass::Int)),
        }
    }

    // performs right-hand operand folding for memory accesses
    fn rhs_operand_rm(&self, rhs: Value, (def, fr, ctx): Ctx<'_, '_, '_, '_>) -> RegMem {
        let base = self.current;

        // if the thing on the right-hand side is a load, we can try to
        // see if we can fold the pointer's source into our instruction
        if pat!(rhs, base, def, ctx, load()) {
            let load = cast!(rhs, def, InstData::Load);
            let ptr = load.pointer();

            // if we were able to perform a second fold, we return that better fold.
            // otherwise, we just return an access to the register where the pointer is
            return if let Some(address) = self.internal_rhs_pointer(ptr, (def, fr, ctx)) {
                RegMem::Mem(address)
            } else {
                RegMem::Mem(IndirectAddress::Reg(ctx.result_reg(ptr, RegClass::Int)))
            };
        }

        RegMem::Reg(ctx.result_reg(rhs, val_class(rhs, def)))
    }

    // performs right-hand operand folding for immediates
    fn rhs_operand_ri(&self, rhs: Value, (def, fr, ctx): Ctx<'_, '_, '_, '_>) -> RegImm {
        match self.internal_rhs_immediate(rhs, (def, fr, ctx)) {
            // if we get any imm8/imm32s, we fold it right in
            Some(imm32) => RegImm::Imm(imm32),
            // if we don't match anything, we just use the register directly
            None => RegImm::Reg(ctx.result_reg(rhs, val_class(rhs, def))),
        }
    }

    // performs right-hand operand folding for immediates and memory accesses
    fn rhs_operand_rmi(&self, rhs: Value, (def, fr, ctx): Ctx<'_, '_, '_, '_>) -> RegMemImm {
        match self.internal_rhs_immediate(rhs, (def, fr, ctx)) {
            // if we get any imm8/imm32s, we fold it right in
            Some(imm32) => RegMemImm::Imm(imm32),
            // if we match any of our optimize-able `mov` patterns, we'll get it here
            None => self.rhs_operand_rm(rhs, (def, fr, ctx)).into(),
        }
    }

    // constrains a value to be put into a specific register, and then generates a mov
    // from that register into a given register to copy it.
    fn mov(
        &self,
        dest: WriteableReg,
        lhs: Value,
        (def, fr, ctx): Ctx<'_, '_, '_, '_>,
    ) -> WriteableReg {
        let class = val_class(lhs, def);
        let src = ctx.result_reg(lhs, class);

        zeroing_mov(dest, RegMemImm::Reg(src), def.dfg.ty(lhs), ctx);

        dest
    }

    fn zero(&self, dest: WriteableReg, ctx: &mut LoweringContext<'module, 'target, X86_64>) {
        ctx.emit(Inst::ALU(ALU {
            opc: ALUOpcode::Xor,
            width: Width::Dword,
            lhs: dest,
            rhs: RegMemImm::Reg(dest.to_reg()),
        }));
    }

    #[inline]
    fn curr_val(&self, def: &'ctx FunctionDefinition) -> Value {
        def.dfg
            .inst_to_result(self.current)
            .expect("attempted to get value for instruction without result")
    }

    #[inline]
    fn curr_result_reg(&self, class: RegClass, (def, fr, ctx): Ctx<'_, '_, '_, '_>) -> Reg {
        ctx.result_reg(self.curr_val(def), class)
    }

    #[inline]
    fn maybe_curr_result_reg(&self, (def, fr, ctx): Ctx<'_, '_, '_, '_>) -> Option<Reg> {
        ctx.maybe_result_reg(def.dfg.inst_to_result(self.current)?)
    }

    fn lower_builtin(
        &mut self,
        func: Func,
        ctx: &mut LoweringContext<'module, 'target, X86_64>,
    ) -> bool {
        let name = ctx.module.function(func).name();

        match name {
            "builtin.x86_64.noop" => ctx.emit(Inst::Nop(Nop { bytes: 1 })),
            _ => return false,
        }

        true
    }

    fn copy_phis_and_jump(
        &mut self,
        target: &BlockWithParams,
        condition: Option<ConditionCode>,
        (def, fr, ctx): Ctx<'_, '_, '_, '_>,
    ) {
        let bb = target.block();
        let args = target.args();

        for (&arg, &param) in iter::zip(args.iter(), def.dfg.block(bb).params()) {
            let class = val_class(param, def);
            let param_reg = ctx.result_reg(param, class);

            self.mov(WriteableReg::from_reg(param_reg), arg, (def, fr, ctx));
        }

        ctx.emit(Inst::Jump(Jump {
            condition,
            target: JumpTarget::Local(ctx.mir_block(bb)),
        }));
    }

    fn signed_division(
        &self,
        data: &ArithInst,
        (def, fr, ctx): Ctx<'_, '_, '_, '_>,
    ) -> (Reg, Width) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let lhs = ctx.result_reg(data.lhs(), RegClass::Int);
        let rhs = self.rhs_operand_rm(data.rhs(), (def, fr, ctx));
        let original_width = value_into_width(data.lhs(), (def, fr, ctx));
        let mut width = original_width;

        // this covers the dividend and the quotient/remainder registers
        ctx.begin_fixed_intervals(&[X86_64::RAX, X86_64::RDX]);

        // IDIV dividend must be located in AX/EAX/RAX
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(lhs),
            dest: WriteableReg::from_reg(IDiv::DIVIDEND_LO),
        }));

        // if we're dealing with 8-bit operands, we sign-extend them to 16-bit
        // due to a limitation of how we represent partial registers (can't model AL vs AH)
        if width == Width::Byte {
            // this is incredibly evil but technically fine, this doesn't actually modify
            // the value at all. the compiler will never be relying on the upper bits
            // when a value is being treated as an i8, and the sign extension won't
            // modify the lower bits that we do rely on
            ctx.emit(Inst::Movsx(Movsx {
                widths: WidthPair::from_widths(Width::Byte, Width::Word),
                src: RegMemImm::Reg(IDiv::DIVIDEND_LO),
                dest: WriteableReg::from_reg(IDiv::DIVIDEND_LO),
            }));

            width = Width::Word;
        }

        // need to sign-extend the dividend into DX:AX/EDX:EAX/RDX:RAX
        match width {
            Width::Byte => unreachable!(),
            Width::Word => ctx.emit(Inst::Cwd(Cwd)),
            Width::Dword => ctx.emit(Inst::Cdq(Cdq)),
            Width::Qword => ctx.emit(Inst::Cqo(Cqo)),
        }

        ctx.emit(Inst::IDiv(IDiv {
            width,
            divisor: rhs,
        }));

        (dest, original_width)
    }

    fn unsigned_division(
        &self,
        data: &ArithInst,
        (def, fr, ctx): Ctx<'_, '_, '_, '_>,
    ) -> (Reg, Width) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let lhs = ctx.result_reg(data.lhs(), RegClass::Int);
        let rhs = self.rhs_operand_rm(data.rhs(), (def, fr, ctx));
        let original_width = value_into_width(data.lhs(), (def, fr, ctx));
        let mut width = original_width;

        // this covers the dividend and the quotient/remainder registers
        ctx.begin_fixed_intervals(&[X86_64::RAX, X86_64::RDX]);

        // DIV dividend must be located in AX/EAX/RAX
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(lhs),
            dest: WriteableReg::from_reg(Div::DIVIDEND_LO),
        }));

        // see signed_division for why this is necessary, we can't deal with partials
        if width == Width::Byte {
            // the upper bits will already be zero, so there's no need to zero-extend or
            // whatever, unlike in the signed case where we need to sign-extend.
            width = Width::Word;
        }

        // need to zero the "upper register" to have our unsigned dividend in DX:AX/EDX:EAX/RDX:RAX
        self.zero(WriteableReg::from_reg(Div::DIVIDEND_HI), ctx);

        ctx.emit(Inst::Div(Div {
            width,
            divisor: rhs,
        }));

        (dest, original_width)
    }
}

impl<'module, 'target> InstructionSelector<'module, 'target, X86_64> for GreedyISel {
    fn new() -> Self {
        Self {
            current: ir::Inst::reserved(),
        }
    }

    fn frame_for_func(
        func: &'module Function,
        target: &Target<X86_64>,
    ) -> Box<dyn StackFrame<X86_64>> {
        // system-v is identical on linux vs macOS
        match func.signature().calling_conv() {
            CallConv::C => target.new_frame(func),
            CallConv::SysV => LinuxX86_64.default_stack_frame(func, target),
            CallConv::Win64 => WindowsX86_64.default_stack_frame(func, target),
        }
    }

    fn lower(
        &mut self,
        inst: ir::Inst,
        func: &'module FunctionDefinition,
        frame: &mut dyn StackFrame<X86_64>,
        ctx: &mut LoweringContext<'module, 'target, X86_64>,
    ) {
        let data = func.dfg.inst_data(inst);

        self.current = inst;
        self.dispatch_inst(data, (func, frame, ctx))
    }
}

macro_rules! alu {
    ($self:expr, $data:expr, $def:expr, $fr:expr, $ctx:expr, $opc:expr) => {{
        let dest = $self.curr_result_reg(RegClass::Int, ($def, $fr, $ctx));
        let lhs = $self.mov(WriteableReg::from_reg(dest), $data.lhs(), ($def, $fr, $ctx));
        let rhs = $self.rhs_operand_rmi($data.rhs(), ($def, $fr, $ctx));
        let width = value_into_width($data.lhs(), ($def, $fr, $ctx));

        $ctx.emit(Inst::ALU(ALU {
            opc: $opc,
            width,
            lhs,
            rhs,
        }));
    }};
}

impl<'mo, 'fr, 'ta, 'ctx> GenericInstVisitor<(), Ctx<'mo, 'fr, 'ta, 'ctx>> for GreedyISel {
    fn visit_call(&mut self, data: &CallInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        if self.lower_builtin(data.callee(), ctx) {
            return;
        }

        let result = self.maybe_curr_result_reg((def, fr, ctx));
        let cc = ctx
            .module
            .function(data.callee())
            .signature()
            .calling_conv();

        let convention = calling_conv(cc, ctx);

        convention.lower_call(data, result.map(WriteableReg::from_reg), (def, fr, ctx));
    }

    fn visit_indirectcall(&mut self, data: &IndirectCallInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_icmp(&mut self, data: &ICmpInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let width = value_into_width(data.lhs(), (def, fr, ctx));
        let class = val_class(data.rhs(), def);
        let lhs = ctx.result_reg(data.lhs(), class);
        let rhs = self.rhs_operand_rmi(data.rhs(), (def, fr, ctx));
        let maybe_result = self.maybe_curr_result_reg((def, fr, ctx));
        let mut zero_optimization = false;

        // this is only needed if the `setCC` is emitted, but it must happen **before** the
        // test/cmp is emitted so it doesn't screw up the condition flags
        if let Some(reg) = maybe_result {
            // we need to make sure to zero the upper bits of the register, since we're only writing a byte
            self.zero(WriteableReg::from_reg(reg), ctx);
        }

        // TODO: right now the `cmp reg, 0` => `test reg, reg` transform is only safe for
        // equality with 0, more work is needed to implement `test` optimizations for
        // other comparisons due to needing to change the jump opcodes used with `condbr`
        if let (RegMemImm::Imm(0), ICmpOp::EQ) = (rhs, data.op()) {
            zero_optimization = true;

            // `test reg, reg` and `cmp reg, 0` are equivalent for our needs
            // the former is slightly more compact in the binary representation
            ctx.emit(Inst::Test(Test {
                width,
                lhs,
                rhs: RegMemImm::Reg(lhs),
            }));
        } else {
            ctx.emit(Inst::Cmp(Cmp { width, lhs, rhs }));
        }

        if let Some(reg) = maybe_result {
            let dest = WriteableReg::from_reg(reg);

            // we do this to get Z instead of E, the two are equivalent but Z is easier to read
            let condition = if zero_optimization {
                ConditionCode::Z
            } else {
                icmp_into_cc(data.op())
            };

            ctx.emit(Inst::Set(Set { condition, dest }));
        }
    }

    fn visit_fcmp(&mut self, data: &FCmpInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_sel(&mut self, data: &SelInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_br(&mut self, data: &BrInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        self.copy_phis_and_jump(data.target(), None, (def, fr, ctx));
    }

    fn visit_condbr(&mut self, data: &CondBrInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let cond = data.condition();
        let cond_source = def.dfg.value_to_inst(cond);

        // basic idea: we can only safely rely on folding checks into the jump if
        // the condition is the previous instruction, and if the condition is an `icmp` or `fcmp`.
        //
        // in that case, we don't constrain the result (since it doesn't need to be in a register)
        // and then directly read the CPU flags
        if def.layout.inst_prev(self.current) == cond_source && def.dfg.uses_of(cond).len() == 1 {
            // if there's no previous instruction AND the condition is a phi, the above `==`
            // could be true and we'd have issues. we need to sanity check that it's a `Some` here
            if let Some(inst) = cond_source {
                let inst_data = def.dfg.inst_data(inst);

                if let InstData::ICmp(icmp) = inst_data {
                    let true_target = data.true_branch();
                    let false_target = data.false_branch();
                    let opc = icmp_into_cc(icmp.op());

                    self.copy_phis_and_jump(true_target, Some(opc), (def, fr, ctx));
                    self.copy_phis_and_jump(false_target, None, (def, fr, ctx));

                    return;
                }

                if let InstData::FCmp(fcmp) = inst_data {
                    //
                }
            }
        }

        // if we don't hit one of the above cases, we fall back on the "inefficient but safe"
        // variant that constraints the result to a register, and then jumps based on that
        // register being zero or not.
        let reg = ctx.result_reg(cond, RegClass::Int);

        ctx.emit(Inst::Test(Test {
            width: Width::Byte,
            lhs: reg,
            rhs: RegMemImm::Reg(reg),
        }));

        ctx.emit(Inst::Jump(Jump {
            condition: Some(ConditionCode::NZ),
            target: JumpTarget::Local(ctx.mir_block(data.true_branch().block())),
        }));

        ctx.emit(Inst::Jump(Jump {
            condition: None,
            target: JumpTarget::Local(ctx.mir_block(data.false_branch().block())),
        }));
    }

    fn visit_unreachable(&mut self, data: &UnreachableInst, (_, _, ctx): Ctx<'_, '_, '_, '_>) {
        // we actually do emit something rather than just nothing. If DCE didn't get
        // any optimizations out of this, it's not worth saving the 2 bytes in return for
        // some extra insanity lying around when the programmer makes a mistake
        ctx.emit(Inst::Ud2(Ud2 {}))
    }

    fn visit_ret(&mut self, data: &RetInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        fr.lower_ret(data, (def, ctx));
    }

    fn visit_and(&mut self, data: &CommutativeArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        alu!(self, data, def, fr, ctx, ALUOpcode::And);
    }

    fn visit_or(&mut self, data: &CommutativeArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        alu!(self, data, def, fr, ctx, ALUOpcode::Or);
    }

    fn visit_xor(&mut self, data: &CommutativeArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let lhs = self.mov(WriteableReg::from_reg(dest), data.lhs(), (def, fr, ctx));
        let rhs = self.rhs_operand_rmi(data.rhs(), (def, fr, ctx));
        let width = value_into_width(data.lhs(), (def, fr, ctx));

        // x ^ -1 => not x
        if pat!(self.current, def, ctx, xor_with(any(), neg1())) {
            ctx.emit(Inst::Neg(Neg { width, reg: lhs }));

            return;
        }

        ctx.emit(Inst::ALU(ALU {
            opc: ALUOpcode::Xor,
            width,
            lhs,
            rhs,
        }));
    }

    fn visit_shl(&mut self, data: &ArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        alu!(self, data, def, fr, ctx, ALUOpcode::Shl);
    }

    fn visit_ashr(&mut self, data: &ArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        alu!(self, data, def, fr, ctx, ALUOpcode::Sar);
    }

    fn visit_lshr(&mut self, data: &ArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        alu!(self, data, def, fr, ctx, ALUOpcode::Shr);
    }

    fn visit_iadd(&mut self, data: &CommutativeArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        alu!(self, data, def, fr, ctx, ALUOpcode::Add);
    }

    fn visit_isub(&mut self, data: &ArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let lhs = self.mov(WriteableReg::from_reg(dest), data.lhs(), (def, fr, ctx));
        let rhs = self.rhs_operand_rmi(data.rhs(), (def, fr, ctx));
        let width = value_into_width(data.lhs(), (def, fr, ctx));

        // 0 - x => neg x
        if pat!(self.current, def, ctx, isub_with(zero(), any())) {
            ctx.emit(Inst::Neg(Neg { width, reg: lhs }));

            return;
        }

        ctx.emit(Inst::ALU(ALU {
            opc: ALUOpcode::Sub,
            width,
            lhs,
            rhs,
        }));
    }

    fn visit_imul(&mut self, data: &CommutativeArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let lhs = self.mov(WriteableReg::from_reg(dest), data.lhs(), (def, fr, ctx));
        let rhs = self.rhs_operand_rmi(data.rhs(), (def, fr, ctx));
        let width = value_into_width(data.lhs(), (def, fr, ctx));

        ctx.emit(Inst::IMul(IMul { width, lhs, rhs }));
    }

    fn visit_sdiv(&mut self, data: &ArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let (dest, width) = self.signed_division(data, (def, fr, ctx));

        // we free RAX back up by moving it into the vreg the result is supposed to be in
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(IDiv::QUOTIENT),
            dest: WriteableReg::from_reg(dest),
        }));

        ctx.end_fixed_intervals(&[X86_64::RAX, X86_64::RDX], 0);
    }

    fn visit_udiv(&mut self, data: &ArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let (dest, width) = self.unsigned_division(data, (def, fr, ctx));

        // we free RDX back up by moving it into the vreg the result is supposed to be in
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(Div::QUOTIENT),
            dest: WriteableReg::from_reg(dest),
        }));

        ctx.end_fixed_intervals(&[X86_64::RAX, X86_64::RDX], 0);
    }

    fn visit_srem(&mut self, data: &ArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let (dest, width) = self.signed_division(data, (def, fr, ctx));

        // we free RDX back up by moving it into the vreg the result is supposed to be in
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(IDiv::REMAINDER),
            dest: WriteableReg::from_reg(dest),
        }));

        ctx.end_fixed_intervals(&[X86_64::RAX, X86_64::RDX], 0);
    }

    fn visit_urem(&mut self, data: &ArithInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let (dest, width) = self.unsigned_division(data, (def, fr, ctx));

        // we free RDX back up by moving it into the vreg the result is supposed to be in
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(Div::REMAINDER),
            dest: WriteableReg::from_reg(dest),
        }));

        ctx.end_fixed_intervals(&[X86_64::RAX, X86_64::RDX], 0);
    }

    fn visit_fneg(&mut self, data: &FloatUnaryInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_fadd(&mut self, data: &CommutativeArithInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_fsub(&mut self, data: &ArithInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_fmul(&mut self, data: &CommutativeArithInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_fdiv(&mut self, data: &ArithInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_frem(&mut self, data: &ArithInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_alloca(&mut self, data: &AllocaInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_load(&mut self, data: &LoadInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let class = val_class(self.curr_val(def), def);
        let dest = self.curr_result_reg(class, (def, fr, ctx));
        let rhs = self.rhs_pointer_indirect_address(data.pointer(), (def, fr, ctx));
        let width = type_into_width(data.result_ty().unwrap(), ctx);

        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Mem(rhs),
            dest: WriteableReg::from_reg(dest),
        }))
    }

    fn visit_store(&mut self, data: &StoreInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let src = self.rhs_operand_ri(data.stored(), (def, fr, ctx));
        let dest = self.rhs_pointer_indirect_address(data.pointer(), (def, fr, ctx));
        let width = type_into_width(def.dfg.ty(data.stored()), ctx);

        ctx.emit(Inst::MovStore(MovStore { width, src, dest }))
    }

    fn visit_offset(&mut self, data: &OffsetInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_extract(&mut self, data: &ExtractInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_insert(&mut self, data: &InsertInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_elemptr(&mut self, data: &ElemPtrInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_sext(&mut self, data: &CastInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let dest_width = type_into_width(data.result_ty().unwrap(), ctx);
        let src_width = value_into_width(data.operand(), (def, fr, ctx));
        let src = self.rhs_operand_rmi(data.operand(), (def, fr, ctx));

        ctx.emit(Inst::Movsx(Movsx {
            widths: WidthPair::from_widths(src_width, dest_width),
            src,
            dest: WriteableReg::from_reg(dest),
        }));
    }

    fn visit_zext(&mut self, data: &CastInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let dest_width = type_into_width(data.result_ty().unwrap(), ctx);
        let src_width = value_into_width(data.operand(), (def, fr, ctx));
        let src = self.rhs_operand_rmi(data.operand(), (def, fr, ctx));

        ctx.emit(Inst::Movzx(Movzx {
            widths: WidthPair::from_widths(src_width, dest_width),
            src,
            dest: WriteableReg::from_reg(dest),
        }));
    }

    fn visit_trunc(&mut self, data: &CastInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));

        // no-op, we just read from the lower bytes of the register later
        self.mov(WriteableReg::from_reg(dest), data.operand(), (def, fr, ctx));
    }

    fn visit_itob(&mut self, data: &CastInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let src = ctx.result_reg(data.operand(), RegClass::Int);
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let width = value_into_width(data.operand(), (def, fr, ctx));

        // we require that true is exactly 1, so we have to do a test-n-set.
        ctx.emit(Inst::Test(Test {
            lhs: src,
            rhs: RegMemImm::Reg(src),
            width,
        }));

        // x & x == 0 only if x == 0, so if non-zero we have true
        ctx.emit(Inst::Set(Set {
            condition: ConditionCode::NZ,
            dest: WriteableReg::from_reg(dest),
        }));
    }

    fn visit_btoi(&mut self, data: &CastInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));

        // the value is already 0 or 1, we just mov to a new register (and assign a result
        // to the bool in the process, forcing it to be emitted properly)
        self.mov(WriteableReg::from_reg(dest), data.operand(), (def, fr, ctx));
    }

    fn visit_sitof(&mut self, data: &CastInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_uitof(&mut self, data: &CastInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_ftosi(&mut self, data: &CastInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_ftoui(&mut self, data: &CastInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_fext(&mut self, data: &CastInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_ftrunc(&mut self, data: &CastInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_itop(&mut self, data: &CastInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));

        // no-op, just mov from old to new vreg
        self.mov(WriteableReg::from_reg(dest), data.operand(), (def, fr, ctx));
    }

    fn visit_ptoi(&mut self, data: &CastInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));

        // no-op, just mov from old to new vreg
        self.mov(WriteableReg::from_reg(dest), data.operand(), (def, fr, ctx));
    }

    fn visit_iconst(&mut self, data: &IConstInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let ty = data.result_ty().unwrap();
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let width = type_into_width(ty, ctx);
        let val = RefCell::new(0);

        // do an efficient zero if we can, we use the whole register with `self.zero`
        if data.value() == 0 {
            self.zero(WriteableReg::from_reg(dest), ctx);

            return;
        }

        // if the value can fit in an imm32 we write it to the register with
        // a dword size minimum to zero the upper bits
        if pat!(self.current, def, ctx, imm32(&val)) {
            ctx.emit(Inst::Mov(Mov {
                src: RegMemImm::Imm(*val.borrow()),
                dest: WriteableReg::from_reg(dest),
                width: width_dword_minimum(width),
            }));

            return;
        }

        // any larger and we need to `movabs` it
        ctx.emit(Inst::Movabs(Movabs {
            dest: WriteableReg::from_reg(dest),
            value: data.value(),
        }));
    }

    fn visit_fconst(&mut self, data: &FConstInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }

    fn visit_bconst(&mut self, data: &BConstInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));

        if data.value() {
            self.zero(WriteableReg::from_reg(dest), ctx);
        } else {
            // we emit it as a `mov` for dwords so that the entire register is cleared
            ctx.emit(Inst::Mov(Mov {
                src: RegMemImm::Imm(1),
                dest: WriteableReg::from_reg(dest),
                width: Width::Dword,
            }));
        }
    }

    fn visit_undef(&mut self, _: &UndefConstInst, _: Ctx<'_, '_, '_, '_>) {
        // do nothing, we have a result register that can be referenced.
        //
        // we don't actually define it, we simply leave it as a new register with
        // no live range (created by `result_reg`) that can be filled in with anything
        // by the register allocator.
    }

    fn visit_null(&mut self, data: &NullConstInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));

        self.zero(WriteableReg::from_reg(dest), ctx);
    }

    fn visit_stackslot(&mut self, data: &StackSlotInst, (def, fr, ctx): Ctx<'_, '_, '_, '_>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, fr, ctx));
        let address = match fr.stack_slot(data.slot(), (def, ctx)) {
            VariableLocation::InReg(_) => unreachable!(),
            VariableLocation::RelativeToSP(offset, stack_size) => {
                IndirectAddress::stack_offset(offset, stack_size)
            }
            VariableLocation::RelativeToFP(offset) => {
                IndirectAddress::RegOffset(Reg::from_preg(X86_64::RBP), offset)
            }
        };

        ctx.emit(Inst::Lea(Lea {
            dest: WriteableReg::from_reg(dest),
            src: address,
        }));
    }

    fn visit_globaladdr(&mut self, data: &GlobalAddrInst, context: Ctx<'_, '_, '_, '_>) {
        todo!()
    }
}
