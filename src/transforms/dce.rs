//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::{
    ControlFlowGraph, ControlFlowGraphAnalysis, DominatorTree, DominatorTreeAnalysis,
};
use crate::arena::SecondaryMap;
use crate::ir::{Cursor, CursorMut, FuncCursor, Function, Instruction, Value};
use crate::pass::{FunctionAnalysisManager, FunctionTransformPass, PreservedAnalyses};
use crate::transforms::common::{has_side_effect, rewrite_and_remove_block_param};
use smallvec::SmallVec;

/// Aggressive dead code elimination.
///
/// This algorithm iterates over a function in postorder, and sees all uses
/// before definitions. It assumes everything (that can't cause side effects)
/// is dead until proven otherwise. It removes everything that it decides is dead.
///
/// This will also remove dead φ nodes from basic blocks, and will remove unreachable
/// blocks entirely.
pub struct DeadCodeEliminationPass;

/// Scans over an entire function and removes dead instructions and φ nodes.
///
/// This implementation is "aggressive," it assumes everything is dead until
/// proven otherwise, and removes everything that is dead.
pub fn aggressive_instruction_dce(
    func: &mut Function,
    cfg: &ControlFlowGraph,
    domtree: &DominatorTree,
) {
    let mut cursor = FuncCursor::over(func);
    let mut live = SecondaryMap::fill(cursor.dfg().next_value(), 0u32);
    let mut params = SmallVec::<[Value; 16]>::new();

    // iterate in postorder, we see uses before defs
    for &block in domtree.postorder() {
        cursor.goto_after(block);

        // iterate blocks backwards for same reason, we need to see uses before defs
        while let Some(inst) = cursor.prev_inst() {
            let is_result_live = cursor
                .inst_to_result(inst)
                .map_or(false, |val| live[val] != 0);

            // this DCE pass considers being used in a branch to be a side effect,
            // but those will be removed later if the block argument itself
            // is unused.
            //
            // other side effects are being used in memory, calls, etc.
            if has_side_effect(cursor.dfg(), inst) || is_result_live {
                for operand in cursor.inst_data(inst).operands() {
                    live[*operand] += 1;
                }

                continue;
            }

            cursor.remove_inst();
        }

        // we don't want to DCE our parameters on the entry block. everything else
        // is fair game though.
        //
        // by this point, if any of the block params are used we'd know it because
        // they would have been marked live earlier. we know for sure that they
        // are unused if they aren't live
        if block != cursor.entry_block().unwrap() {
            params.extend(cursor.block_params(block).iter().copied());

            for param in params.drain(..) {
                if live[param] != 0 {
                    continue;
                }

                // we don't need to update liveness information of these, when we get
                // to the rewritten branches it will check that info with the
                // current state of the branches.
                rewrite_and_remove_block_param(&mut cursor, cfg, block, param);
            }
        }
    }
}

impl FunctionTransformPass for DeadCodeEliminationPass {
    fn run(&mut self, func: &mut Function, am: &mut FunctionAnalysisManager) -> PreservedAnalyses {
        let cfg = am.get::<ControlFlowGraphAnalysis>(func);
        let domtree = am.get::<DominatorTreeAnalysis>(func);

        aggressive_instruction_dce(func, &cfg, &domtree);

        PreservedAnalyses::none()
    }
}