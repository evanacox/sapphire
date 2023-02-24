//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use super::common::InPlaceConstantFolder;
use crate::analysis::{ControlFlowGraphAnalysis, DominatorTree, DominatorTreeAnalysis};
use crate::arena::ArenaKey;
use crate::ir::matchers::*;
use crate::ir::*;
use crate::pass::*;
use crate::transforms::common::has_side_effect;
use std::mem;

/// A "simplify all the instructions" pass. This is the algebraic simplification
/// pass, although it will do some trivial constant folding as well. This is
/// not a full constant propagation pass, but things like `iadd 1, 1` will be
/// simplified. Notably, it will not simplify any branches, although it may simplify
/// their conditions.
///
/// This combines three main jobs:
///
/// 1. Canonicalization
/// 2. Trivial Constant Folding
/// 3. Peephole Optimizations
pub struct SimplifyInstPass;

impl FunctionTransformPass for SimplifyInstPass {
    fn run(&mut self, func: &mut Function, am: &mut FunctionAnalysisManager) -> PreservedAnalyses {
        let domtree = am.get::<DominatorTreeAnalysis>(func);
        let visitor = SimplifyVisitor::new(func, &domtree);

        visitor.walk();

        let mut preserved = PreservedAnalyses::none();

        preserved.preserve::<ControlFlowGraphAnalysis>();
        preserved.preserve::<DominatorTreeAnalysis>();

        preserved
    }
}

struct SimplifyVisitor<'f> {
    cursor: FuncCursor<'f>,
    rpo: Vec<Block>,
    worklist: Vec<(Simplification<'f>, Inst)>,
    // context is a stack. simplifications push context they need onto it, and
    // the simplifications are run in reverse order so they can pop their context back
    context: Vec<u64>,
}

impl<'f> SimplifyVisitor<'f> {
    fn new(func: &'f mut Function, domtree: &DominatorTree) -> Self {
        Self {
            cursor: FuncCursor::over(func),
            rpo: domtree.reverse_postorder().collect(),
            worklist: Vec::default(),
            context: Vec::default(),
        }
    }

    // returns if the replacer should replace with swapped operands.
    //
    // there are four cases we care about:
    //   - lhs is constant, rhs is not: should swap always to move the constant
    //   - lhs is not, rhs is constant: should never swap
    //   - lhs is constant, rhs is constant: should swap based on lhs.value > rhs.value
    //   - neither are constant: should swap if lhs value number is larger
    fn should_sort_binary_ops(&mut self, lhs: Value, rhs: Value) -> bool {
        match (
            self.cursor.value_to_inst(lhs),
            self.cursor.value_to_inst(rhs),
        ) {
            (Some(i_lhs), Some(i_rhs)) => {
                let i_lhs = self.cursor.inst_data(i_lhs);
                let i_rhs = self.cursor.inst_data(i_rhs);

                match (i_lhs.is_constant(), i_rhs.is_constant()) {
                    (true, true) => i_lhs.constant_raw() > i_rhs.constant_raw(),
                    (true, false) => true,
                    (false, true) => false,
                    (false, false) => lhs.key_index() > rhs.key_index(),
                }
            }
            _ => lhs.key_index() > rhs.key_index(),
        }
    }

    fn matches_inst<'a>(&'a self, inst: Inst, matcher: impl IRMatcher<'a>) -> bool {
        matches_inst(inst, matcher, self.cursor.dfg())
    }

    fn matches<'a>(&'a self, val: Value, matcher: impl IRMatcher<'a>) -> bool {
        matches(val, matcher, self.cursor.dfg())
    }

    fn inst(&self) -> Inst {
        self.cursor.current_inst().unwrap()
    }
}

impl<'f> FunctionCursorVisitor<'f, Option<Simplification<'f>>, FuncCursor<'f>>
    for SimplifyVisitor<'f>
{
    fn cursor(&mut self) -> &mut FuncCursor<'f> {
        &mut self.cursor
    }

    fn result(self) -> Option<Simplification<'f>> {
        None
    }

    fn walk(mut self) -> Option<Simplification<'f>> {
        self.dispatch_blocks();

        // if the worklist has anything in it, run all the simplifications
        // and then try to refill the worklist. repeat until no more simplifications are found
        while !self.worklist.is_empty() {
            while let Some((work, inst)) = self.worklist.pop() {
                let dbg = self.cursor.inst_debug(inst);
                let data = self.cursor.inst_data(inst).clone();

                self.cursor.goto_inst(inst);

                (work)(&mut self, dbg, &data);
            }

            self.dispatch_blocks();
        }

        None
    }

    fn dispatch_blocks(&mut self) {
        // stupid, but you can't iterate over self.rpo while calling `self.visit_block`
        let rpo = mem::take(&mut self.rpo);

        for bb in rpo.iter().copied() {
            self.visit_block(bb);
        }

        self.rpo = rpo;
    }

    fn dispatch_insts(&mut self, block: Block) {
        self.cursor().goto_before(block);

        while let Some(inst) = self.cursor().next_inst() {
            if let Some(simplification) = self.visit_inst(inst) {
                self.worklist.push((simplification, inst));
            }
        }
    }

    fn visit_inst(&mut self, inst: Inst) -> Option<Simplification<'f>> {
        // we intentionally don't want to screw with branches here
        if !has_side_effect(self.cursor.dfg(), inst) {
            let data = self.cursor.inst_data(inst).clone();

            // we already did the fold, so we return a "simplification" that we "perform" later
            // for the sake of the worklist making sense.
            if InPlaceConstantFolder::try_fold(inst, &data, &mut self.cursor) {
                return Some(|_, _, _| {});
            }

            return self.dispatch_inst(&data);
        }

        None
    }
}

macro_rules! try_sort_commutative_binary_ops {
    ($self:expr, $inst:expr, $ty:path, $name:ident) => {
        if $self.should_sort_binary_ops($inst.lhs(), $inst.rhs()) {
            return Some(|this, dbg, data| {
                let inst = cast!($ty, data);

                this.cursor.replace().$name(inst.rhs(), inst.lhs(), dbg);
            });
        }
    };
}

macro_rules! cast {
    ($pat:path, $target:expr) => {{
        if let $pat(a) = $target {
            a
        } else {
            panic!("mismatch variant when cast to {}", stringify!($pat))
        }
    }};
}

macro_rules! cast_val {
    ($pat:path, $self:expr, $target:expr) => {{
        if let $pat(a) = $self
            .cursor
            .inst_data($self.cursor.value_to_inst($target).unwrap())
        {
            a
        } else {
            panic!("mismatch variant when cast to {}", stringify!($pat))
        }
    }};
}

type Simplification<'f> = fn(&mut SimplifyVisitor<'f>, DebugInfo, &InstData);

impl<'f> GenericInstVisitor<Option<Simplification<'f>>> for SimplifyVisitor<'f> {
    fn visit_call(&mut self, _: &CallInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_indirectcall(&mut self, _: &IndirectCallInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_icmp(&mut self, icmp: &ICmpInst) -> Option<Simplification<'f>> {
        if self.should_sort_binary_ops(icmp.lhs(), icmp.rhs()) {
            Some(|this, dbg, data| {
                let icmp = cast!(InstData::ICmp, data);

                this.cursor
                    .replace()
                    .icmp(icmp.op(), icmp.rhs(), icmp.lhs(), dbg);
            })
        } else {
            None
        }
    }

    fn visit_fcmp(&mut self, fcmp: &FCmpInst) -> Option<Simplification<'f>> {
        if self.should_sort_binary_ops(fcmp.lhs(), fcmp.rhs()) {
            Some(|this, dbg, data| {
                let fcmp = cast!(InstData::FCmp, data);

                this.cursor
                    .replace()
                    .fcmp(fcmp.op(), fcmp.rhs(), fcmp.lhs(), dbg);
            })
        } else {
            None
        }
    }

    fn visit_sel(&mut self, _: &SelInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_br(&mut self, _: &BrInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_condbr(&mut self, _: &CondBrInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_unreachable(&mut self, _: &UnreachableInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_ret(&mut self, _: &RetInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_and(&mut self, and: &CommutativeArithInst) -> Option<Simplification<'f>> {
        try_sort_commutative_binary_ops!(self, and, InstData::And, and);

        None
    }

    fn visit_or(&mut self, or: &CommutativeArithInst) -> Option<Simplification<'f>> {
        try_sort_commutative_binary_ops!(self, or, InstData::Or, or);

        None
    }

    fn visit_xor(&mut self, xor: &CommutativeArithInst) -> Option<Simplification<'f>> {
        try_sort_commutative_binary_ops!(self, xor, InstData::Xor, xor);

        None
    }

    fn visit_shl(&mut self, _: &ArithInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_ashr(&mut self, _: &ArithInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_lshr(&mut self, _: &ArithInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_iadd(&mut self, iadd: &CommutativeArithInst) -> Option<Simplification<'f>> {
        try_sort_commutative_binary_ops!(self, iadd, InstData::IAdd, iadd);

        None
    }

    fn visit_isub(&mut self, _: &ArithInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_imul(&mut self, imul: &CommutativeArithInst) -> Option<Simplification<'f>> {
        try_sort_commutative_binary_ops!(self, imul, InstData::IMul, imul);

        // imul %0, <power of 2>
        if self.matches_inst(self.inst(), imul_with(val(), power_of_two())) {
            let rhs = cast_val!(InstData::IConst, self, imul.rhs()).value();

            self.context.push(rhs.ilog2() as u64);

            // x * <pow2> => x << log2(<power of 2>)
            return Some(|this, dbg, data| {
                let imul = cast!(InstData::IMul, data);
                let shift = this.context.pop().unwrap();
                let log2_rhs = this
                    .cursor()
                    .insert()
                    .iconst(imul.result_ty().unwrap(), shift, dbg);

                this.cursor().replace().shl(imul.lhs(), log2_rhs, dbg);
            });
        }

        None
    }

    fn visit_sdiv(&mut self, _: &ArithInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_udiv(&mut self, inst: &ArithInst) -> Option<Simplification<'f>> {
        // udiv %0, <power of 2>
        if self.matches_inst(self.inst(), udiv_with(val(), power_of_two())) {
            let rhs = cast_val!(InstData::IConst, self, inst.rhs()).value();

            self.context.push(rhs.ilog2() as u64);

            // x / <pow2> => x >> (log2(<power of 2>))
            return Some(|this, dbg, data| {
                let udiv = cast!(InstData::UDiv, data);
                let shift = this.context.pop().unwrap();
                let log2_rhs = this
                    .cursor()
                    .insert()
                    .iconst(udiv.result_ty().unwrap(), shift, dbg);

                this.cursor().replace().lshr(udiv.lhs(), log2_rhs, dbg);
            });
        }

        None
    }

    fn visit_srem(&mut self, _: &ArithInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_urem(&mut self, inst: &ArithInst) -> Option<Simplification<'f>> {
        // urem %0, <power of 2>
        if self.matches_inst(self.inst(), urem_with(val(), power_of_two())) {
            let rhs = cast_val!(InstData::IConst, self, inst.rhs()).value();

            self.context.push(rhs);

            // x % <pow2> => x & (<pow2> - 1)
            return Some(|this, dbg, data| {
                let urem = cast!(InstData::URem, data);
                let and_val = this.context.pop().unwrap() - 1;
                let rhs_sub_1 = this //
                    .cursor()
                    .insert()
                    .iconst(urem.result_ty().unwrap(), and_val, dbg);

                this.cursor().replace().and(urem.lhs(), rhs_sub_1, dbg);
            });
        }

        None
    }

    fn visit_fneg(&mut self, _: &FloatUnaryInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_fadd(&mut self, fadd: &CommutativeArithInst) -> Option<Simplification<'f>> {
        try_sort_commutative_binary_ops!(self, fadd, InstData::FAdd, fadd);

        None
    }

    fn visit_fsub(&mut self, _: &ArithInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_fmul(&mut self, fmul: &CommutativeArithInst) -> Option<Simplification<'f>> {
        try_sort_commutative_binary_ops!(self, fmul, InstData::FMul, fmul);

        None
    }

    fn visit_fdiv(&mut self, _: &ArithInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_frem(&mut self, _: &ArithInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_alloca(&mut self, _: &AllocaInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_load(&mut self, _: &LoadInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_store(&mut self, _: &StoreInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_offset(&mut self, _: &OffsetInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_extract(&mut self, _: &ExtractInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_insert(&mut self, _: &InsertInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_elemptr(&mut self, _: &ElemPtrInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_sext(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_zext(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_trunc(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_itob(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_btoi(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_sitof(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_uitof(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_ftosi(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_ftoui(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_fext(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_ftrunc(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_itop(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_ptoi(&mut self, _: &CastInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_iconst(&mut self, _: &IConstInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_fconst(&mut self, _: &FConstInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_bconst(&mut self, _: &BConstInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_undef(&mut self, _: &UndefConstInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_null(&mut self, _: &NullConstInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_stackslot(&mut self, _: &StackSlotInst) -> Option<Simplification<'f>> {
        None
    }

    fn visit_globaladdr(&mut self, _: &GlobalAddrInst) -> Option<Simplification<'f>> {
        None
    }
}
