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
use std::marker::PhantomData;

/// An instruction selector for x86-64.
///
/// This selector uses the greedy "maximal munch" principle for matching
/// instruction patterns. This may be slower than other selectors that pick
/// the first valid instruction pattern.
pub struct GreedyISel<Abi>
where
    Abi: ABI<X86_64>,
{
    current: ir::Inst,
    _unused: PhantomData<fn() -> Abi>,
}

macro_rules! pat {
    ($val:expr, $base:expr, $def:expr, $ctx:expr, $matcher:expr) => {
        merge_if_matches_operand($val, $base, ($def, $ctx), $matcher)
    };

    ($base:expr, $def:expr, $ctx:expr, $matcher:expr) => {
        merge_if_matches($base, ($def, $ctx), $matcher)
    };
}

fn value_into_width<Abi: ABI<X86_64>>(val: Value, (def, ctx): Ctx<'_, '_, '_, Abi>) -> Width {
    type_into_width(def.dfg.ty(val), ctx)
}

fn type_into_width<Abi: ABI<X86_64>>(
    ty: Type,
    ctx: &mut LoweringContext<'_, '_, X86_64, Abi, Inst>,
) -> Width {
    let size = ctx.target.layout_of(ty);

    Width::from_bytes(size.size() as usize)
}

fn width_dword_minimum(width: Width) -> Width {
    match width {
        Width::Byte | Width::Word => Width::Dword,
        x => x,
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

impl<'module, 'target, 'ctx, Abi> GreedyISel<Abi>
where
    'module: 'ctx,
    'target: 'ctx,
    Abi: ABI<X86_64>,
{
    // performs right-hand operand folding for memory accesses
    fn rhs_operand_rm(&self, rhs: Value, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) -> RegMem {
        // TODO

        RegMem::Reg(ctx.result_reg(rhs, self.val_class(rhs, def)))
    }

    // performs right-hand operand folding for immediates and memory accesses
    fn rhs_operand_rmi(
        &self,
        rhs: Value,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) -> RegMemImm {
        let base = self.current;
        let val = RefCell::new(0);

        // any imm8/imm32 we immediately fold into the instruction
        if pat!(rhs, base, def, ctx, imm32(&val)) {
            return RegMemImm::Imm(*val.borrow());
        }

        // if we match any of our optimize-able `mov` patterns, we'll get it here
        self.rhs_operand_rm(rhs, (def, ctx)).into()
    }

    // constrains a value to be put into a specific register, and then generates a mov
    // from that register into a given register to copy it.
    fn mov(
        &self,
        dest: WriteableReg,
        lhs: Value,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) -> WriteableReg {
        let class = self.val_class(lhs, def);
        let src = ctx.result_reg(lhs, class);
        let width = width_dword_minimum(value_into_width(lhs, (def, ctx)));

        // we emit it as a `mov` for dwords so that the entire register is cleared
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(src),
            dest,
        }));

        dest
    }

    fn zero(&self, dest: WriteableReg, (_, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        ctx.emit(Inst::ALU(ALU {
            opc: ALUOpcode::Xor,
            width: Width::Dword,
            lhs: dest,
            rhs: RegMemImm::Reg(dest.to_reg()),
        }));
    }

    #[inline(always)]
    fn val_class(&self, val: Value, def: &'ctx FunctionDefinition) -> RegClass {
        match def.dfg.ty(val).unpack() {
            UType::Float(_) => RegClass::Float,
            UType::Int(_) | UType::Bool(_) | UType::Ptr(_) => RegClass::Int,
            UType::Array(_) | UType::Struct(_) => {
                panic!("unable to put array or structure in physical register")
            }
        }
    }

    #[inline(always)]
    fn curr_val(&self, def: &'ctx FunctionDefinition) -> Value {
        def.dfg
            .inst_to_result(self.current)
            .expect("attempted to get value for instruction without result")
    }

    #[inline(always)]
    fn curr_result_reg(
        &self,
        class: RegClass,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) -> Reg {
        ctx.result_reg(self.curr_val(def), class)
    }

    #[inline(always)]
    fn maybe_curr_result_reg(&self, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) -> Option<Reg> {
        ctx.maybe_result_reg(self.curr_val(def))
    }

    fn lower_builtin(
        &mut self,
        func: Func,
        ctx: &mut LoweringContext<'module, 'target, X86_64, Abi, Inst>,
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
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        let bb = target.block();
        let args = target.args();

        for (&arg, &param) in iter::zip(args.iter(), def.dfg.block(bb).params()) {
            let class = self.val_class(param, def);
            let param_reg = ctx.result_reg(param, class);

            self.mov(WriteableReg::from_reg(param_reg), arg, (def, ctx));
        }

        ctx.emit(Inst::Jump(Jump {
            condition,
            target: JumpTarget::Local(ctx.mir_block(bb)),
        }));
    }

    fn signed_division(
        &self,
        data: &ArithInst,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) -> (Reg, Width) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));
        let lhs = ctx.result_reg(data.lhs(), RegClass::Int);
        let rhs = self.rhs_operand_rm(data.rhs(), (def, ctx));
        let mut width = value_into_width(data.lhs(), (def, ctx));

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

        (dest, width)
    }

    fn unsigned_division(
        &self,
        data: &ArithInst,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) -> (Reg, Width) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));
        let lhs = ctx.result_reg(data.lhs(), RegClass::Int);
        let rhs = self.rhs_operand_rm(data.rhs(), (def, ctx));
        let mut width = value_into_width(data.lhs(), (def, ctx));

        // DIV dividend must be located in AX/EAX/RAX
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(lhs),
            dest: WriteableReg::from_reg(Div::DIVIDEND_LO),
        }));

        // if we're dealing with 8-bit operands, we sign-extend them to 16-bit
        // due to a limitation of how we represent partial registers (can't model AL vs AH)
        if width == Width::Byte {
            // this is incredibly evil but technically fine, this doesn't actually modify
            // the value at all. the compiler will never be relying on the upper bits
            // when a value is being treated as an i8, and the zero extension won't
            // modify the lower bits that we do rely on
            ctx.emit(Inst::Movzx(Movzx {
                widths: WidthPair::from_widths(Width::Byte, Width::Word),
                src: RegMemImm::Reg(Div::DIVIDEND_LO),
                dest: WriteableReg::from_reg(Div::DIVIDEND_LO),
            }));

            width = Width::Word;
        }

        // need to zero the "upper register" to have our unsigned dividend in DX:AX/EDX:EAX/RDX:RAX
        self.zero(WriteableReg::from_reg(Div::DIVIDEND_HI), (def, ctx));

        ctx.emit(Inst::Div(Div {
            width,
            divisor: rhs,
        }));

        (dest, width)
    }
}

impl<'module, 'target, Abi> InstructionSelector<'module, 'target, X86_64, Abi, Inst>
    for GreedyISel<Abi>
where
    Abi: ABI<X86_64>,
{
    fn new() -> Self {
        Self {
            current: ir::Inst::reserved(),
            _unused: PhantomData::default(),
        }
    }

    fn lower(
        &mut self,
        inst: ir::Inst,
        func: &'module FunctionDefinition,
        ctx: &mut LoweringContext<'module, 'target, X86_64, Abi, Inst>,
    ) {
        let data = func.dfg.inst_data(inst);

        self.current = inst;
        self.dispatch_inst(data, (func, ctx))
    }
}

type Ctx<'module, 'target, 'ctx, Abi> =
    crate::codegen::Ctx<'module, 'target, 'ctx, X86_64, Abi, x86_64::Inst>;

macro_rules! alu {
    ($self:expr, $data:expr, $def:expr, $ctx:expr, $opc:expr) => {{
        let dest = $self.curr_result_reg(RegClass::Int, ($def, $ctx));
        let lhs = $self.mov(WriteableReg::from_reg(dest), $data.lhs(), ($def, $ctx));
        let rhs = $self.rhs_operand_rmi($data.rhs(), ($def, $ctx));
        let width = value_into_width($data.lhs(), ($def, $ctx));

        $ctx.emit(Inst::ALU(ALU {
            opc: $opc,
            width,
            lhs,
            rhs,
        }));
    }};
}

impl<'module, 'target, 'ctx, Abi> GenericInstVisitor<(), Ctx<'module, 'target, 'ctx, Abi>>
    for GreedyISel<Abi>
where
    Abi: ABI<X86_64>,
{
    fn visit_call(&mut self, data: &CallInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        if self.lower_builtin(data.callee(), ctx) {
            return;
        }

        todo!()
    }

    fn visit_indirectcall(
        &mut self,
        data: &IndirectCallInst,
        context: Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        todo!()
    }

    fn visit_icmp(&mut self, data: &ICmpInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let width = value_into_width(data.lhs(), (def, ctx));
        let class = self.val_class(data.rhs(), def);
        let lhs = ctx.result_reg(data.lhs(), class);
        let rhs = self.rhs_operand_rmi(data.rhs(), (def, ctx));
        let maybe_result = self.maybe_curr_result_reg((def, ctx));
        let mut zero_optimization = false;

        // this is only needed if the `setCC` is emitted, but it must happen **before** the
        // test/cmp is emitted so it doesn't screw up the condition flags
        if let Some(reg) = maybe_result {
            // we need to make sure to zero the upper bits of the register, since we're only writing a byte
            self.zero(WriteableReg::from_reg(reg), (def, ctx));
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

    fn visit_fcmp(&mut self, data: &FCmpInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_sel(&mut self, data: &SelInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_br(&mut self, data: &BrInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        self.copy_phis_and_jump(data.target(), None, (def, ctx));
    }

    fn visit_condbr(&mut self, data: &CondBrInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
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

                    self.copy_phis_and_jump(true_target, Some(opc), (def, ctx));
                    self.copy_phis_and_jump(false_target, None, (def, ctx));

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

    fn visit_unreachable(
        &mut self,
        data: &UnreachableInst,
        context: Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        todo!()
    }

    fn visit_ret(&mut self, data: &RetInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        if let Some(val) = data.value() {
            let out = Reg::from_preg(X86_64::RAX);

            self.mov(WriteableReg::from_reg(out), val, (def, ctx));
        }

        ctx.emit(Inst::Ret(Ret {}));
    }

    fn visit_and(
        &mut self,
        data: &CommutativeArithInst,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        alu!(self, data, def, ctx, ALUOpcode::And);
    }

    fn visit_or(
        &mut self,
        data: &CommutativeArithInst,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        alu!(self, data, def, ctx, ALUOpcode::Or);
    }

    fn visit_xor(
        &mut self,
        data: &CommutativeArithInst,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));
        let lhs = self.mov(WriteableReg::from_reg(dest), data.lhs(), (def, ctx));
        let rhs = self.rhs_operand_rmi(data.rhs(), (def, ctx));
        let width = value_into_width(data.lhs(), (def, ctx));

        // x ^ -1 => not x
        if pat!(self.current, def, ctx, xor_with(any(), neg1())) {
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

    fn visit_shl(&mut self, data: &ArithInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        alu!(self, data, def, ctx, ALUOpcode::Shl);
    }

    fn visit_ashr(&mut self, data: &ArithInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        alu!(self, data, def, ctx, ALUOpcode::Sar);
    }

    fn visit_lshr(&mut self, data: &ArithInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        alu!(self, data, def, ctx, ALUOpcode::Shr);
    }

    fn visit_iadd(
        &mut self,
        data: &CommutativeArithInst,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        alu!(self, data, def, ctx, ALUOpcode::Add);
    }

    fn visit_isub(&mut self, data: &ArithInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));
        let lhs = self.mov(WriteableReg::from_reg(dest), data.lhs(), (def, ctx));
        let rhs = self.rhs_operand_rmi(data.rhs(), (def, ctx));
        let width = value_into_width(data.lhs(), (def, ctx));

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

    fn visit_imul(
        &mut self,
        data: &CommutativeArithInst,
        (def, ctx): Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));
        let lhs = self.mov(WriteableReg::from_reg(dest), data.lhs(), (def, ctx));
        let rhs = self.rhs_operand_rmi(data.rhs(), (def, ctx));
        let width = value_into_width(data.lhs(), (def, ctx));

        ctx.emit(Inst::IMul(IMul { width, lhs, rhs }));
    }

    fn visit_sdiv(&mut self, data: &ArithInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let (dest, width) = self.signed_division(data, (def, ctx));

        // we free RAX back up by moving it into the vreg the result is supposed to be in
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(IDiv::QUOTIENT),
            dest: WriteableReg::from_reg(dest),
        }));
    }

    fn visit_udiv(&mut self, data: &ArithInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let (dest, width) = self.unsigned_division(data, (def, ctx));

        // we free RDX back up by moving it into the vreg the result is supposed to be in
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(Div::QUOTIENT),
            dest: WriteableReg::from_reg(dest),
        }));
    }

    fn visit_srem(&mut self, data: &ArithInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let (dest, width) = self.signed_division(data, (def, ctx));

        // we free RDX back up by moving it into the vreg the result is supposed to be in
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(IDiv::REMAINDER),
            dest: WriteableReg::from_reg(dest),
        }));
    }

    fn visit_urem(&mut self, data: &ArithInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let (dest, width) = self.unsigned_division(data, (def, ctx));

        // we free RDX back up by moving it into the vreg the result is supposed to be in
        ctx.emit(Inst::Mov(Mov {
            width,
            src: RegMemImm::Reg(Div::REMAINDER),
            dest: WriteableReg::from_reg(dest),
        }));
    }

    fn visit_fneg(&mut self, data: &FloatUnaryInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_fadd(
        &mut self,
        data: &CommutativeArithInst,
        context: Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        todo!()
    }

    fn visit_fsub(&mut self, data: &ArithInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_fmul(
        &mut self,
        data: &CommutativeArithInst,
        context: Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        todo!()
    }

    fn visit_fdiv(&mut self, data: &ArithInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_frem(&mut self, data: &ArithInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_alloca(&mut self, data: &AllocaInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_load(&mut self, data: &LoadInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_store(&mut self, data: &StoreInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_offset(&mut self, data: &OffsetInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_extract(&mut self, data: &ExtractInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_insert(&mut self, data: &InsertInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_elemptr(&mut self, data: &ElemPtrInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_sext(&mut self, data: &CastInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));
        let dest_width = type_into_width(data.result_ty().unwrap(), ctx);
        let src_width = value_into_width(data.operand(), (def, ctx));
        let src = self.rhs_operand_rmi(data.operand(), (def, ctx));

        ctx.emit(Inst::Movsx(Movsx {
            widths: WidthPair::from_widths(src_width, dest_width),
            src,
            dest: WriteableReg::from_reg(dest),
        }));
    }

    fn visit_zext(&mut self, data: &CastInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));
        let dest_width = type_into_width(data.result_ty().unwrap(), ctx);
        let src_width = value_into_width(data.operand(), (def, ctx));
        let src = self.rhs_operand_rmi(data.operand(), (def, ctx));

        ctx.emit(Inst::Movzx(Movzx {
            widths: WidthPair::from_widths(src_width, dest_width),
            src,
            dest: WriteableReg::from_reg(dest),
        }));
    }

    fn visit_trunc(&mut self, data: &CastInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));

        // no-op, we just read from the lower bytes of the register later
        self.mov(WriteableReg::from_reg(dest), data.operand(), (def, ctx));
    }

    fn visit_itob(&mut self, data: &CastInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));

        // we don't have any requirement on true being 1, it just has to be non-zero.
        // so we just do a mov. non-zero becomes "true" and zero becomes "false"
        self.mov(WriteableReg::from_reg(dest), data.operand(), (def, ctx));
    }

    fn visit_btoi(&mut self, data: &CastInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));
        let width = width_dword_minimum(type_into_width(data.result_ty().unwrap(), ctx));

        // we're only getting 0 or 1, no need to emit a whole zext. just set the whole register
        // to that no matter what the width is
        self.mov(WriteableReg::from_reg(dest), data.operand(), (def, ctx));
        ctx.emit(Inst::ALU(ALU {
            opc: ALUOpcode::And,
            lhs: WriteableReg::from_reg(dest),
            rhs: RegMemImm::Imm(1),
            width,
        }));
    }

    fn visit_sitof(&mut self, data: &CastInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_uitof(&mut self, data: &CastInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_ftosi(&mut self, data: &CastInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_ftoui(&mut self, data: &CastInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_fext(&mut self, data: &CastInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_ftrunc(&mut self, data: &CastInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_itop(&mut self, data: &CastInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));

        // no-op, just mov from old to new vreg
        self.mov(WriteableReg::from_reg(dest), data.operand(), (def, ctx));
    }

    fn visit_ptoi(&mut self, data: &CastInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));

        // no-op, just mov from old to new vreg
        self.mov(WriteableReg::from_reg(dest), data.operand(), (def, ctx));
    }

    fn visit_iconst(&mut self, data: &IConstInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let ty = data.result_ty().unwrap();
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));
        let width = type_into_width(ty, ctx);
        let val = RefCell::new(0);

        // do an efficient zero if we can, we use the whole register with `self.zero`
        if data.value() == 0 {
            self.zero(WriteableReg::from_reg(dest), (def, ctx));

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

    fn visit_fconst(&mut self, data: &FConstInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_bconst(&mut self, data: &BConstInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));

        if data.value() {
            self.zero(WriteableReg::from_reg(dest), (def, ctx));
        } else {
            // we emit it as a `mov` for dwords so that the entire register is cleared
            ctx.emit(Inst::Mov(Mov {
                src: RegMemImm::Imm(1),
                dest: WriteableReg::from_reg(dest),
                width: Width::Dword,
            }));
        }
    }

    fn visit_undef(&mut self, _: &UndefConstInst, _: Ctx<'module, 'target, 'ctx, Abi>) {
        // do nothing, we have a result register that can be referenced
    }

    fn visit_null(&mut self, data: &NullConstInst, (def, ctx): Ctx<'module, 'target, 'ctx, Abi>) {
        let dest = self.curr_result_reg(RegClass::Int, (def, ctx));

        self.zero(WriteableReg::from_reg(dest), (def, ctx));
    }

    fn visit_stackslot(&mut self, data: &StackSlotInst, context: Ctx<'module, 'target, 'ctx, Abi>) {
        todo!()
    }

    fn visit_globaladdr(
        &mut self,
        data: &GlobalAddrInst,
        context: Ctx<'module, 'target, 'ctx, Abi>,
    ) {
        todo!()
    }
}
