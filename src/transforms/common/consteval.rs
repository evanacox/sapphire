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

macro_rules! generic_as_constant {
    ($self:expr, $val:expr, $t:ident, $f:ident, $null:expr) => {
        match $self.cursor.value_def($val) {
            ValueDef::Inst(i) => match $self.cursor.inst_data(i) {
                InstData::$t(inst) => Some($f(inst)),
                InstData::Null(_) => Some($null),
                _ => None,
            },
            ValueDef::Param(_, _) => None,
        }
    };
}

/// A generic "fold this instruction if possible" utility. It perform
/// transforms similar to the following:
///
/// ```none
/// %0 = iconst i32 42
/// %1 = iconst i32 6
/// %2 = iadd i32 %0, %1 ; -> `%2 = iconst i32 48`
/// ```
///
/// Note that this will fold illegal operations (e.g. a `load null` or
/// `sdiv 1, 0`) into `unreachable`s.
///
/// Notable exceptions that it will never fold are floating-point operations
/// due to the target-dependent behavior.
///
/// Note that this is an extremely naive transform, it will happily generate
/// the same constant over and over again. A GVN and a DCE pass after using
/// this will likely be necessary.
pub struct InPlaceConstantFolder<'f, 'c> {
    cursor: &'c mut FuncCursor<'f>,
    inst: Inst,
}

impl<'f, 'c> InPlaceConstantFolder<'f, 'c> {
    /// Attempts to perform trivial constant folding on a single instruction.
    ///
    /// Returns whether or not the folder was able to make a simplification.
    pub fn try_fold(inst: Inst, data: &InstData, cursor: &'c mut FuncCursor<'f>) -> bool {
        // TODO: redesign this so we don't need to clone every single instruction that we even attempt to fold
        let mut obj = Self { cursor, inst };

        obj.dispatch_inst(data, ()).is_some()
    }

    fn val_is_constant(&self, val: Value) -> bool {
        match self.cursor.value_def(val) {
            ValueDef::Inst(i) => self.inst_is_constant(i),
            ValueDef::Param(_, _) => false,
        }
    }

    fn inst_is_constant(&self, inst: Inst) -> bool {
        self.cursor.inst_data(inst).is_constant()
    }

    fn val_as_int_constant(&self, val: Value) -> Option<u64> {
        let map = |inst: &IConstInst| inst.value();

        generic_as_constant!(self, val, IConst, map, 0)
    }

    fn val_as_bool_constant(&self, val: Value) -> Option<bool> {
        let map = |inst: &BConstInst| inst.value();

        generic_as_constant!(self, val, BConst, map, false)
    }

    fn val_is_nullptr(&self, val: Value) -> bool {
        match self.cursor.value_def(val) {
            ValueDef::Inst(i) => self.inst_is_constant(i) && self.cursor.ty(val).is_ptr(),
            ValueDef::Param(_, _) => false,
        }
    }

    fn dbg(&self) -> DebugInfo {
        self.cursor.current_inst_dbg().unwrap()
    }
}

macro_rules! icmp_comparison_set {
    ($ty:ty) => {
        [
            |a, b| (a as $ty) > (b as $ty),
            |a, b| (a as $ty) < (b as $ty),
            |a, b| (a as $ty) >= (b as $ty),
            |a, b| (a as $ty) <= (b as $ty),
        ]
    };
}

impl<'f, 'c> GenericInstVisitor<Option<()>, ()> for InPlaceConstantFolder<'f, 'c> {
    fn visit_call(&mut self, _: &CallInst, _: ()) -> Option<()> {
        None
    }

    fn visit_indirectcall(&mut self, _: &IndirectCallInst, _: ()) -> Option<()> {
        None
    }

    fn visit_icmp(&mut self, data: &ICmpInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(data.lhs())?;
        let rhs = self.val_as_int_constant(data.rhs())?;
        let dbg = self.dbg();

        const U8_FNS: [fn(u64, u64) -> bool; 4] = icmp_comparison_set!(u8);
        const U16_FNS: [fn(u64, u64) -> bool; 4] = icmp_comparison_set!(u16);
        const U32_FNS: [fn(u64, u64) -> bool; 4] = icmp_comparison_set!(u32);
        const U64_FNS: [fn(u64, u64) -> bool; 4] = icmp_comparison_set!(u64);
        const I8_FNS: [fn(u64, u64) -> bool; 4] = icmp_comparison_set!(i8);
        const I16_FNS: [fn(u64, u64) -> bool; 4] = icmp_comparison_set!(i16);
        const I32_FNS: [fn(u64, u64) -> bool; 4] = icmp_comparison_set!(i32);
        const I64_FNS: [fn(u64, u64) -> bool; 4] = icmp_comparison_set!(i64);

        let curr_fns = match self.cursor.ty(data.lhs()).unwrap_int().width() {
            8 => [U8_FNS, I8_FNS],
            16 => [U16_FNS, I16_FNS],
            32 => [U32_FNS, I32_FNS],
            64 => [U64_FNS, I64_FNS],
            _ => unreachable!(),
        };

        let check = match data.op() {
            ICmpOp::EQ => |lhs, rhs| lhs == rhs,
            ICmpOp::NE => |lhs, rhs| lhs != rhs,
            ICmpOp::SGT => curr_fns[1][0],
            ICmpOp::SLT => curr_fns[1][1],
            ICmpOp::SGE => curr_fns[1][2],
            ICmpOp::SLE => curr_fns[1][3],
            ICmpOp::UGT => curr_fns[0][0],
            ICmpOp::ULT => curr_fns[0][1],
            ICmpOp::UGE => curr_fns[0][2],
            ICmpOp::ULE => curr_fns[0][3],
        };

        self.cursor.replace().bconst(check(lhs, rhs), dbg);

        Some(())
    }

    fn visit_fcmp(&mut self, _: &FCmpInst, _: ()) -> Option<()> {
        None
    }

    fn visit_sel(&mut self, data: &SelInst, _: ()) -> Option<()> {
        let cond = self.val_as_bool_constant(data.condition())?;
        let curr = self
            .cursor
            .dfg()
            .inst_to_result(self.cursor.current_inst().unwrap())
            .unwrap();

        if cond {
            self.cursor.replace_uses_with(curr, data.if_true());
        } else {
            self.cursor.replace_uses_with(curr, data.if_false());
        }

        self.cursor.remove_inst();

        Some(())
    }

    fn visit_br(&mut self, _: &BrInst, _: ()) -> Option<()> {
        None
    }

    fn visit_condbr(&mut self, _: &CondBrInst, _: ()) -> Option<()> {
        None
    }

    fn visit_unreachable(&mut self, _: &UnreachableInst, _: ()) -> Option<()> {
        None
    }

    fn visit_ret(&mut self, _: &RetInst, _: ()) -> Option<()> {
        None
    }

    fn visit_and(&mut self, and: &CommutativeArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(and.lhs())?;
        let rhs = self.val_as_int_constant(and.rhs())?;
        let ty = self.cursor.ty(and.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor
            .replace()
            .iconst(ty, (lhs & rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_or(&mut self, or: &CommutativeArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(or.lhs())?;
        let rhs = self.val_as_int_constant(or.rhs())?;
        let ty = self.cursor.ty(or.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor
            .replace()
            .iconst(ty, (lhs | rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_xor(&mut self, xor: &CommutativeArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(xor.lhs())?;
        let rhs = self.val_as_int_constant(xor.rhs())?;
        let ty = self.cursor.ty(xor.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor
            .replace()
            .iconst(ty, (lhs ^ rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_shl(&mut self, shl: &ArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(shl.lhs())?;
        let rhs = self.val_as_int_constant(shl.rhs())?;
        let ty = self.cursor.ty(shl.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor
            .replace()
            .iconst(ty, (lhs << rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_ashr(&mut self, ashr: &ArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(ashr.lhs())?;
        let rhs = self.val_as_int_constant(ashr.rhs())?;
        let ty = self.cursor.ty(ashr.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        // we need to cast to i64 here so we get arithmetic right shift behavior
        self.cursor.replace().iconst(
            ty,
            (((lhs as i64) >> (rhs as i64)) as u64) & ty.unwrap_int().mask(),
            dbg,
        );

        Some(())
    }

    fn visit_lshr(&mut self, lshr: &ArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(lshr.lhs())?;
        let rhs = self.val_as_int_constant(lshr.rhs())?;
        let ty = self.cursor.ty(lshr.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        // we need to cast to i64 here so we get arithmetic right shift behavior
        self.cursor
            .replace()
            .iconst(ty, (lhs >> rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_iadd(&mut self, iadd: &CommutativeArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(iadd.lhs())?;
        let rhs = self.val_as_int_constant(iadd.rhs())?;
        let ty = self.cursor.ty(iadd.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor
            .replace()
            .iconst(ty, (lhs + rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_isub(&mut self, isub: &ArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(isub.lhs())?;
        let rhs = self.val_as_int_constant(isub.rhs())?;
        let ty = self.cursor.ty(isub.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor
            .replace()
            .iconst(ty, (lhs - rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_imul(&mut self, imul: &CommutativeArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(imul.lhs())?;
        let rhs = self.val_as_int_constant(imul.rhs())?;
        let ty = self.cursor.ty(imul.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor
            .replace()
            .iconst(ty, (lhs * rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_sdiv(&mut self, sdiv: &ArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(sdiv.lhs())?;
        let rhs = self.val_as_int_constant(sdiv.rhs())?;

        if rhs == 0 {
            return None;
        }

        let ty = self.cursor.ty(sdiv.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor.replace().iconst(
            ty,
            (((lhs as i64) / (rhs as i64)) as u64) & ty.unwrap_int().mask(),
            dbg,
        );

        Some(())
    }

    fn visit_udiv(&mut self, udiv: &ArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(udiv.lhs())?;
        let rhs = self.val_as_int_constant(udiv.rhs())?;
        let ty = self.cursor.ty(udiv.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor
            .replace()
            .iconst(ty, (lhs / rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_srem(&mut self, srem: &ArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(srem.lhs())?;
        let rhs = self.val_as_int_constant(srem.rhs())?;

        if rhs == 0 {
            return None;
        }

        let ty = self.cursor.ty(srem.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor.replace().iconst(
            ty,
            (((lhs as i64) % (rhs as i64)) as u64) & ty.unwrap_int().mask(),
            dbg,
        );

        Some(())
    }

    fn visit_urem(&mut self, urem: &ArithInst, _: ()) -> Option<()> {
        let lhs = self.val_as_int_constant(urem.lhs())?;
        let rhs = self.val_as_int_constant(urem.rhs())?;
        let ty = self.cursor.ty(urem.lhs());
        let dbg = self.cursor.current_inst_dbg().unwrap();

        self.cursor
            .replace()
            .iconst(ty, (lhs % rhs) & ty.unwrap_int().mask(), dbg);

        Some(())
    }

    fn visit_fneg(&mut self, _: &FloatUnaryInst, _: ()) -> Option<()> {
        None
    }

    fn visit_fadd(&mut self, _: &CommutativeArithInst, _: ()) -> Option<()> {
        None
    }

    fn visit_fsub(&mut self, _: &ArithInst, _: ()) -> Option<()> {
        None
    }

    fn visit_fmul(&mut self, _: &CommutativeArithInst, _: ()) -> Option<()> {
        None
    }

    fn visit_fdiv(&mut self, _: &ArithInst, _: ()) -> Option<()> {
        None
    }

    fn visit_frem(&mut self, _: &ArithInst, _: ()) -> Option<()> {
        None
    }

    fn visit_alloca(&mut self, _: &AllocaInst, _: ()) -> Option<()> {
        None
    }

    fn visit_load(&mut self, _: &LoadInst, _: ()) -> Option<()> {
        None
    }

    fn visit_store(&mut self, _: &StoreInst, _: ()) -> Option<()> {
        None
    }

    fn visit_offset(&mut self, _: &OffsetInst, _: ()) -> Option<()> {
        None
    }

    fn visit_extract(&mut self, _: &ExtractInst, _: ()) -> Option<()> {
        None
    }

    fn visit_insert(&mut self, _: &InsertInst, _: ()) -> Option<()> {
        None
    }

    fn visit_elemptr(&mut self, _: &ElemPtrInst, _: ()) -> Option<()> {
        None
    }

    fn visit_sext(&mut self, _: &CastInst, _: ()) -> Option<()> {
        None
    }

    fn visit_zext(&mut self, _: &CastInst, _: ()) -> Option<()> {
        None
    }

    fn visit_trunc(&mut self, _: &CastInst, _: ()) -> Option<()> {
        None
    }

    fn visit_itob(&mut self, data: &CastInst, _: ()) -> Option<()> {
        let val = self.val_as_int_constant(data.operand())?;
        let dbg = self.dbg();

        self.cursor.replace().bconst(val != 0, dbg);

        Some(())
    }

    fn visit_btoi(&mut self, data: &CastInst, _: ()) -> Option<()> {
        let val = self.val_as_bool_constant(data.operand())?;
        let dbg = self.dbg();

        self.cursor
            .replace()
            .iconst(data.result_ty().unwrap(), val as u64, dbg);

        Some(())
    }

    fn visit_sitof(&mut self, _: &CastInst, _: ()) -> Option<()> {
        None
    }

    fn visit_uitof(&mut self, _: &CastInst, _: ()) -> Option<()> {
        None
    }

    fn visit_ftosi(&mut self, _: &CastInst, _: ()) -> Option<()> {
        None
    }

    fn visit_ftoui(&mut self, _: &CastInst, _: ()) -> Option<()> {
        None
    }

    fn visit_fext(&mut self, _: &CastInst, _: ()) -> Option<()> {
        None
    }

    fn visit_ftrunc(&mut self, _: &CastInst, _: ()) -> Option<()> {
        None
    }

    fn visit_itop(&mut self, data: &CastInst, _: ()) -> Option<()> {
        let val = self.val_as_int_constant(data.operand())?;

        if val == 0 {
            let dbg = self.dbg();

            self.cursor.replace().null(Type::ptr(), dbg);

            Some(())
        } else {
            None
        }
    }

    fn visit_ptoi(&mut self, data: &CastInst, _: ()) -> Option<()> {
        if self.val_is_nullptr(data.operand()) {
            let dbg = self.dbg();

            self.cursor
                .replace()
                .iconst(data.result_ty().unwrap(), 0, dbg);

            Some(())
        } else {
            None
        }
    }

    fn visit_iconst(&mut self, _: &IConstInst, _: ()) -> Option<()> {
        None
    }

    fn visit_fconst(&mut self, _: &FConstInst, _: ()) -> Option<()> {
        None
    }

    fn visit_bconst(&mut self, _: &BConstInst, _: ()) -> Option<()> {
        None
    }

    fn visit_undef(&mut self, _: &UndefConstInst, _: ()) -> Option<()> {
        None
    }

    fn visit_null(&mut self, _: &NullConstInst, _: ()) -> Option<()> {
        None
    }

    fn visit_stackslot(&mut self, _: &StackSlotInst, _: ()) -> Option<()> {
        None
    }

    fn visit_globaladdr(&mut self, _: &GlobalAddrInst, _: ()) -> Option<()> {
        None
    }
}
