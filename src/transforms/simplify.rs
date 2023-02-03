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
use crate::ir::*;
use crate::pass::*;
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
pub struct InstSimplifyPass;

impl FunctionTransformPass for InstSimplifyPass {
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
}

impl<'f> SimplifyVisitor<'f> {
    fn new(func: &'f mut Function, domtree: &DominatorTree) -> Self {
        Self {
            cursor: FuncCursor::over(func),
            rpo: domtree.reverse_postorder().collect(),
        }
    }
}

impl<'f> FunctionCursorVisitor<'f, (), FuncCursor<'f>> for SimplifyVisitor<'f> {
    fn cursor(&mut self) -> &mut FuncCursor<'f> {
        &mut self.cursor
    }

    fn result(self) {}

    fn dispatch_blocks(&mut self) {
        // stupid, but you can't iterate over self.rpo while calling `self.visit_block`
        for bb in mem::take(&mut self.rpo) {
            self.visit_block(bb);
        }
    }

    fn visit_inst(&mut self, inst: Inst) {
        // we intentionally don't want to screw with branches here
        if self.cursor.dfg().branch_info(inst).is_none() {
            InPlaceConstantFolder::try_fold(inst, self.cursor());
        }
    }
}

impl<'f> GenericInstVisitor<()> for SimplifyVisitor<'f> {
    fn visit_call(&mut self, _: &CallInst) {}

    fn visit_indirectcall(&mut self, _: &IndirectCallInst) {}

    fn visit_icmp(&mut self, _: &ICmpInst) {}

    fn visit_fcmp(&mut self, _: &FCmpInst) {}

    fn visit_sel(&mut self, _: &SelInst) {}

    fn visit_br(&mut self, _: &BrInst) {}

    fn visit_condbr(&mut self, _: &CondBrInst) {}

    fn visit_unreachable(&mut self, _: &UnreachableInst) {}

    fn visit_ret(&mut self, _: &RetInst) {}

    fn visit_and(&mut self, _: &CommutativeArithInst) {}

    fn visit_or(&mut self, _: &CommutativeArithInst) {}

    fn visit_xor(&mut self, _: &CommutativeArithInst) {}

    fn visit_shl(&mut self, _: &ArithInst) {}

    fn visit_ashr(&mut self, _: &ArithInst) {}

    fn visit_lshr(&mut self, _: &ArithInst) {}

    fn visit_iadd(&mut self, _: &CommutativeArithInst) {}

    fn visit_isub(&mut self, _: &ArithInst) {}

    fn visit_imul(&mut self, _: &CommutativeArithInst) {}

    fn visit_sdiv(&mut self, _: &ArithInst) {}

    fn visit_udiv(&mut self, _: &ArithInst) {}

    fn visit_srem(&mut self, _: &ArithInst) {}

    fn visit_urem(&mut self, _: &ArithInst) {}

    fn visit_fneg(&mut self, _: &FloatUnaryInst) {}

    fn visit_fadd(&mut self, _: &ArithInst) {}

    fn visit_fsub(&mut self, _: &ArithInst) {}

    fn visit_fmul(&mut self, _: &ArithInst) {}

    fn visit_fdiv(&mut self, _: &ArithInst) {}

    fn visit_frem(&mut self, _: &ArithInst) {}

    fn visit_alloca(&mut self, _: &AllocaInst) {}

    fn visit_load(&mut self, _: &LoadInst) {}

    fn visit_store(&mut self, _: &StoreInst) {}

    fn visit_offset(&mut self, _: &OffsetInst) {}

    fn visit_extract(&mut self, _: &ExtractInst) {}

    fn visit_insert(&mut self, _: &InsertInst) {}

    fn visit_elemptr(&mut self, _: &ElemPtrInst) {}

    fn visit_sext(&mut self, _: &CastInst) {}

    fn visit_zext(&mut self, _: &CastInst) {}

    fn visit_trunc(&mut self, _: &CastInst) {}

    fn visit_itob(&mut self, _: &CastInst) {}

    fn visit_btoi(&mut self, _: &CastInst) {}

    fn visit_sitof(&mut self, _: &CastInst) {}

    fn visit_uitof(&mut self, _: &CastInst) {}

    fn visit_ftosi(&mut self, _: &CastInst) {}

    fn visit_ftoui(&mut self, _: &CastInst) {}

    fn visit_fext(&mut self, _: &CastInst) {}

    fn visit_ftrunc(&mut self, _: &CastInst) {}

    fn visit_itop(&mut self, _: &CastInst) {}

    fn visit_ptoi(&mut self, _: &CastInst) {}

    fn visit_iconst(&mut self, _: &IConstInst) {}

    fn visit_fconst(&mut self, _: &FConstInst) {}

    fn visit_bconst(&mut self, _: &BConstInst) {}

    fn visit_undef(&mut self, _: &UndefConstInst) {}

    fn visit_null(&mut self, _: &NullConstInst) {}

    fn visit_globaladdr(&mut self, _: &GlobalAddrInst) {}
}
