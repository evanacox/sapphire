//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::*;

macro_rules! into_cast {
    ($var:ident, $self:expr, into: ($into:expr, $into_should_be:ident), from: ($from:expr, $from_should_be:ident), $debug:expr) => {{
        debug_assert!($into.$into_should_be());
        debug_assert!($self.dfg().ty($from).$from_should_be());

        $self.build_result(InstData::$var(CastInst::new($into, $from)), $debug)
    }};
}

macro_rules! integer_cast {
    ($var:ident, $self:expr, $into:expr, $from:expr, from_width $op:tt into_width, $debug:expr) => {{
        let from = $self.dfg().ty($from);

        debug_assert!($into.is_int(), "result must be integer");
        debug_assert!(from.is_int(), "operand must be integer");
        debug_assert!((from.unwrap_int().width() $op $into.unwrap_int().width()),
            concat!("operand width must be ", stringify!($op), " output width"));

        $self.build_result(InstData::$var(CastInst::new($into, $from)), $debug)
    }}
}

macro_rules! base_binary_inst {
    ($t:ident, $var:ident, $self:expr, operands: (lhs: $lhs:expr, rhs: $rhs:expr, check: $check:ident), $debug:expr) => {{
        let lhs_ty = $self.dfg().ty($lhs);

        debug_assert_eq!(
            $self.dfg().ty($lhs),
            $self.dfg().ty($rhs),
            "operands must be same type"
        );
        debug_assert!(lhs_ty.$check());

        let inst = $t::new(lhs_ty, $lhs, $rhs);

        $self.build_result(InstData::$var(inst), $debug)
    }};
}

macro_rules! commutative_arith_bit {
    ($var:ident, $self:expr, operands: ($lhs:expr, $rhs:expr), $debug:expr) => {{
        base_binary_inst!(
            CommutativeArithInst,
            $var,
            $self,
            operands: (lhs: $lhs, rhs: $rhs, check: is_bool_or_int),
            $debug
        )
    }};
}

macro_rules! commutative_arith_integral {
    ($var:ident, $self:expr, operands: ($lhs:expr, $rhs:expr), $debug:expr) => {{
        base_binary_inst!(CommutativeArithInst, $var, $self, operands: (lhs: $lhs, rhs: $rhs, check: is_int), $debug)
    }};
}

macro_rules! arith_integral {
    ($var:ident, $self:expr, operands: (lhs: $lhs:expr, rhs: $rhs:expr), $debug:expr) => {{
        base_binary_inst!(ArithInst, $var, $self, operands: (lhs: $lhs, rhs: $rhs, check: is_int), $debug)
    }};
}

macro_rules! arith_float {
    ($var:ident, $self:expr, operands: (lhs: $lhs:expr, rhs: $rhs:expr), $debug:expr) => {{
        base_binary_inst!(ArithInst, $var, $self, operands: (lhs: $lhs, rhs: $rhs, check: is_float), $debug)
    }};
}

macro_rules! commutative_arith_float {
    ($var:ident, $self:expr, operands: (lhs: $lhs:expr, rhs: $rhs:expr), $debug:expr) => {{
        base_binary_inst!(CommutativeArithInst, $var, $self, operands: (lhs: $lhs, rhs: $rhs, check: is_float), $debug)
    }};
}

/// Helper trait that allows easy creation of instruction builders. This trait
/// provides a variety of helper methods that build instructions and inserts them
/// in whatever way the trait implementor defines.
///
/// This is used for the append/insert/replace builders, along with any
/// other more situational ones scattered around the codebase.
pub trait InstBuilder<'dfg>: Sized {
    /// Gets the data-flow graph in use for the inserter
    fn dfg(&self) -> &DataFlowGraph;

    /// "Builds" a single instruction and inserts it in whatever way
    /// the particular [`InstBuilder`] sees fit.
    ///
    /// This returns a reference to the instruction and possibly a
    /// reference to the result of that instruction.
    fn build(self, data: InstData, debug: DebugInfo) -> (Inst, Option<Value>);

    /// Builds an instruction and returns its result.
    fn build_result(self, data: InstData, debug: DebugInfo) -> Value {
        self.build(data, debug)
            .1
            .expect("expected a result for instruction")
    }

    /// Builds an instruction and returns the instruction
    fn build_inst(self, data: InstData, debug: DebugInfo) -> Inst {
        self.build(data, debug).0
    }

    /// Builds a `call` instruction to a statically-known function.
    fn call(self, callee: Func, sig: Sig, args: &[Value], debug: DebugInfo) -> Inst {
        let output = self.dfg().signature(sig).return_ty();
        let call = CallInst::new(output, sig, callee, args);

        self.build_inst(InstData::Call(call), debug)
    }

    /// Builds an `indirectcall` instruction to a statically-known function.
    fn indirectcall(self, callee: Value, sig: Sig, args: &[Value], debug: DebugInfo) -> Inst {
        debug_assert_eq!(self.dfg().ty(callee), Type::ptr());

        let output = self.dfg().signature(sig).return_ty();
        let call = IndirectCallInst::new(output, sig, callee, args);

        self.build_inst(InstData::IndirectCall(call), debug)
    }

    /// Builds an `icmp` instruction
    fn icmp(self, cmp: ICmpOp, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        debug_assert_eq!(self.dfg().ty(lhs), self.dfg().ty(rhs));
        debug_assert!({
            let ty = self.dfg().ty(lhs);

            ty.is_bool_or_int() || ty.is_ptr()
        });

        let icmp = ICmpInst::new(cmp, lhs, rhs);

        self.build_result(InstData::ICmp(icmp), debug)
    }

    /// Builds an `icmp eq` instruction
    fn icmp_eq(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        self.icmp(ICmpOp::EQ, lhs, rhs, debug)
    }

    /// Builds an `icmp ne` instruction
    fn icmp_ne(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        self.icmp(ICmpOp::NE, lhs, rhs, debug)
    }

    /// Builds an `fcmp` instruction
    fn fcmp(self, cmp: FCmpOp, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        debug_assert_eq!(self.dfg().ty(lhs), self.dfg().ty(rhs));
        debug_assert!(self.dfg().ty(lhs).is_float());

        let fcmp = FCmpInst::new(cmp, lhs, rhs);

        self.build_result(InstData::FCmp(fcmp), debug)
    }

    /// Builds a `sel` instruction
    fn sel(self, cond: Value, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        debug_assert_eq!(self.dfg().ty(lhs), self.dfg().ty(rhs));
        debug_assert_eq!(self.dfg().ty(cond), Type::bool());

        let sel = SelInst::new(self.dfg().ty(lhs), cond, lhs, rhs);

        self.build_result(InstData::Sel(sel), debug)
    }

    /// Builds a `br` instruction
    fn br(self, target: BlockWithParams, debug: DebugInfo) -> Inst {
        debug_assert!(self.dfg().is_block_inserted(target.block()));

        let br = BrInst::new(target);

        self.build_inst(InstData::Br(br), debug)
    }

    /// Builds a `condbr` instruction
    fn condbr(
        self,
        cond: Value,
        if_true: BlockWithParams,
        if_false: BlockWithParams,
        debug: DebugInfo,
    ) -> Inst {
        debug_assert!(self.dfg().is_block_inserted(if_true.block()));
        debug_assert!(self.dfg().is_block_inserted(if_false.block()));
        debug_assert_eq!(self.dfg().ty(cond), Type::bool());

        let cbr = CondBrInst::new(cond, if_true, if_false);

        self.build_inst(InstData::CondBr(cbr), debug)
    }

    /// Builds an `unreachable` instruction
    fn unreachable(self, debug: DebugInfo) -> Inst {
        self.build_inst(InstData::Unreachable(UnreachableInst::new()), debug)
    }

    /// Builds a `ret` instruction that possibly returns a value
    /// and possibly returns `void`.
    fn ret(self, value: Option<Value>, debug: DebugInfo) -> Inst {
        self.build_inst(InstData::Ret(RetInst::new(value)), debug)
    }

    /// Shorthand for [`Self::ret`] with a `Some`.
    fn ret_val(self, value: Value, debug: DebugInfo) -> Inst {
        self.ret(Some(value), debug)
    }

    /// Shorthand for [`Self::ret`] with a `None`.
    fn ret_void(self, debug: DebugInfo) -> Inst {
        self.ret(None, debug)
    }

    /// Builds an `and` instruction
    fn and(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        commutative_arith_bit!(And, self, operands: (lhs, rhs), debug)
    }

    /// Builds an `or` instruction
    fn or(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        commutative_arith_bit!(Or, self, operands: (lhs, rhs), debug)
    }

    /// Builds an `xor` instruction
    fn xor(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        commutative_arith_bit!(Xor, self, operands: (lhs, rhs), debug)
    }

    /// Builds a `shl` instruction
    fn shl(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_integral!(Shl, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `ashr` instruction
    fn ashr(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_integral!(AShr, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds a `lshr` instruction
    fn lshr(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_integral!(LShr, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `iadd` instruction
    fn iadd(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        commutative_arith_integral!(IAdd, self, operands: (lhs, rhs), debug)
    }

    /// Builds an `isub` instruction
    fn isub(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_integral!(ISub, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `imul` instruction
    fn imul(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        commutative_arith_integral!(IMul, self, operands: (lhs, rhs), debug)
    }

    /// Builds an `sdiv` instruction
    fn sdiv(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_integral!(SDiv, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds a `udiv` instruction
    fn udiv(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_integral!(UDiv, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `srem` instruction
    fn srem(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_integral!(SRem, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds a `urem` instruction
    fn urem(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_integral!(URem, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `fneg` instruction
    fn fneg(self, val: Value, debug: DebugInfo) -> Value {
        debug_assert!(self.dfg().ty(val).is_float());

        let lhs_ty = self.dfg().ty(val);
        let fneg = FloatUnaryInst::new(lhs_ty, val);

        self.build_result(InstData::FNeg(fneg), debug)
    }

    /// Builds an `fadd` instruction
    fn fadd(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        commutative_arith_float!(FAdd, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `fsub` instruction
    fn fsub(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_float!(FSub, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `fmul` instruction
    fn fmul(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        commutative_arith_float!(FMul, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `fdiv` instruction
    fn fdiv(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_float!(FDiv, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `frem` instruction
    fn frem(self, lhs: Value, rhs: Value, debug: DebugInfo) -> Value {
        arith_float!(FRem, self, operands: (lhs: lhs, rhs: rhs), debug)
    }

    /// Builds an `alloca` instruction
    fn alloca(self, ty: Type, debug: DebugInfo) -> Value {
        self.build_result(InstData::Alloca(AllocaInst::new(ty)), debug)
    }

    /// Builds a non-volatile `load` instruction
    fn load(self, ty: Type, ptr: Value, debug: DebugInfo) -> Value {
        debug_assert_eq!(self.dfg().ty(ptr), Type::ptr());

        let inst = LoadInst::new(ptr, ty, false);

        self.build_result(InstData::Load(inst), debug)
    }

    /// Builds a volatile `load` instruction
    fn load_volatile(self, ty: Type, ptr: Value, debug: DebugInfo) -> Value {
        debug_assert_eq!(self.dfg().ty(ptr), Type::ptr());

        let inst = LoadInst::new(ptr, ty, true);

        self.build_result(InstData::Load(inst), debug)
    }

    /// Builds a non-volatile `store` instruction
    fn store(self, val: Value, ptr: Value, debug: DebugInfo) -> Inst {
        debug_assert_eq!(self.dfg().ty(ptr), Type::ptr());

        let inst = StoreInst::new(ptr, val, false);

        self.build_inst(InstData::Store(inst), debug)
    }

    /// Builds a volatile `store` instruction
    fn store_volatile(self, val: Value, ptr: Value, debug: DebugInfo) -> Inst {
        debug_assert_eq!(self.dfg().ty(ptr), Type::ptr());

        let inst = StoreInst::new(ptr, val, true);

        self.build_inst(InstData::Store(inst), debug)
    }

    /// Builds an `offset` instruction
    fn offset(self, ty: Type, ptr: Value, offset: Value, debug: DebugInfo) -> Value {
        debug_assert_eq!(self.dfg().ty(ptr), Type::ptr());
        debug_assert!(self.dfg().ty(offset).is_int());

        let inst = OffsetInst::new(ptr, offset, ty);

        self.build_result(InstData::Offset(inst), debug)
    }

    /// Builds an `extract` instruction that extracts a value of a given type
    fn extract(self, output: Type, agg: Value, index: u64, debug: DebugInfo) -> Value {
        let inst = ExtractInst::new(output, agg, index);

        self.build_result(InstData::Extract(inst), debug)
    }

    /// Builds an `insert` instruction
    fn insert(self, agg: Value, val: Value, index: u64, debug: DebugInfo) -> Value {
        let ty = self.dfg().ty(agg);
        let inst = InsertInst::new(ty, agg, val, index);

        self.build_result(InstData::Insert(inst), debug)
    }

    /// Builds an `elemptr` instruction
    fn elemptr(self, ty: Type, ptr: Value, index: u64, debug: DebugInfo) -> Value {
        debug_assert!(ty.is_struct() || ty.is_array());

        let inst = ElemPtrInst::new(ty, ptr, index);

        self.build_result(InstData::ElemPtr(inst), debug)
    }

    /// Builds a `sext` instruction
    fn sext(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        integer_cast!(Sext, self, into, from, from_width < into_width, debug)
    }

    /// Builds a `zext` instruction
    fn zext(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        integer_cast!(Zext, self, into, from, from_width < into_width, debug)
    }

    /// Builds a `trunc` instruction
    fn trunc(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        integer_cast!(Trunc, self, into, from, from_width > into_width, debug)
    }

    /// Builds an `itob` instruction
    fn itob(self, from: Value, debug: DebugInfo) -> Value {
        into_cast!(
            IToB,
            self,
            into: (Type::bool(), is_bool),
            from: (from, is_int),
            debug
        )
    }

    /// Builds a `btoi` instruction
    fn btoi(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        into_cast!(
            BToI,
            self,
            into: (into, is_int),
            from: (from, is_bool),
            debug
        )
    }

    /// Builds a `sitof` instruction
    fn sitof(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        into_cast!(
            SIToF,
            self,
            into: (into, is_float),
            from: (from, is_int),
            debug
        )
    }

    /// Builds a `uitof` instruction
    fn uitof(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        into_cast!(
            UIToF,
            self,
            into: (into, is_float),
            from: (from, is_int),
            debug
        )
    }

    /// Builds an `ftosi` instruction
    fn ftosi(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        into_cast!(
            FToSI,
            self,
            into: (into, is_int),
            from: (from, is_float),
            debug
        )
    }

    /// Builds an `ftoui` instruction
    fn ftoui(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        into_cast!(
            FToUI,
            self,
            into: (into, is_int),
            from: (from, is_float),
            debug
        )
    }

    /// Builds an `fext` instruction
    fn fext(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        debug_assert!(self.dfg().ty(from).is_float_of_format(FloatFormat::Single));
        debug_assert!(into.is_float_of_format(FloatFormat::Double));
        into_cast!(
            FExt,
            self,
            into: (into, is_float),
            from: (from, is_float),
            debug
        )
    }

    /// Builds an `fext` instruction
    fn ftrunc(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        debug_assert!(self.dfg().ty(from).is_float_of_format(FloatFormat::Double));
        debug_assert!(into.is_float_of_format(FloatFormat::Single));
        into_cast!(
            FTrunc,
            self,
            into: (into, is_float),
            from: (from, is_float),
            debug
        )
    }

    /// Builds an `itop` instruction
    fn itop(self, from: Value, debug: DebugInfo) -> Value {
        into_cast!(
            IToP,
            self,
            into: (Type::ptr(), is_ptr),
            from: (from, is_int),
            debug
        )
    }

    /// Builds a `ptoi` instruction
    fn ptoi(self, into: Type, from: Value, debug: DebugInfo) -> Value {
        into_cast!(
            PToI,
            self,
            into: (into, is_int),
            from: (from, is_ptr),
            debug
        )
    }

    /// Builds an `iconst` instruction
    fn iconst(self, into: Type, from: u64, debug: DebugInfo) -> Value {
        debug_assert!(into.is_int());

        self.build_result(InstData::IConst(IConstInst::new(into, from)), debug)
    }

    /// Builds an `fconst` instruction
    fn fconst(self, into: Type, from: f64, debug: DebugInfo) -> Value {
        self.fconst_raw(into, from.to_bits(), debug)
    }

    /// Builds an `fconst` instruction
    fn fconst_raw(self, into: Type, raw: u64, debug: DebugInfo) -> Value {
        debug_assert!(into.is_float());

        self.build_result(InstData::FConst(FConstInst::new(into, raw)), debug)
    }

    /// Builds a `bconst` instruction
    fn bconst(self, value: bool, debug: DebugInfo) -> Value {
        self.build_result(InstData::BConst(BConstInst::new(value)), debug)
    }

    /// Builds an `undef` instruction
    fn undef(self, into: Type, debug: DebugInfo) -> Value {
        self.build_result(InstData::Undef(UndefConstInst::new(into)), debug)
    }

    /// Builds a `null` instruction
    fn null(self, into: Type, debug: DebugInfo) -> Value {
        self.build_result(InstData::Null(NullConstInst::new(into)), debug)
    }

    /// Builds a `stackslot` instruction
    fn stackslot(self, slot: StackSlot, debug: DebugInfo) -> Value {
        self.build_result(InstData::StackSlot(StackSlotInst::new(slot)), debug)
    }

    /// Builds a `globaladdr` instruction
    fn globaladdr(self, global: String, debug: DebugInfo) -> Value {
        self.build_result(InstData::GlobalAddr(GlobalAddrInst::new(global)), debug)
    }
}
