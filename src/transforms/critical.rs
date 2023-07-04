//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::{ControlFlowGraph, ControlFlowGraphAnalysis};
use crate::ir::{Block, BlockWithParams, Cursor, CursorMut, FuncCursor, Function, InstBuilder};
use crate::pass::{FunctionAnalysisManager, FunctionTransformPass, PreservedAnalyses};
use crate::utility::Packable;

/// Performs critical-edge splitting.
///
/// Each edge that is split has a dummy node inserted that contains only an
/// unconditional branch to the block that was originally being targeted.
pub struct SplitCriticalEdges;

impl FunctionTransformPass for SplitCriticalEdges {
    fn run(&mut self, func: &mut Function, am: &mut FunctionAnalysisManager) -> PreservedAnalyses {
        let cfg = am.get::<ControlFlowGraphAnalysis>(func);

        split_crit_edges(func, &cfg);

        PreservedAnalyses::none()
    }
}

/// Performs critical edge splitting over a function. Each edge that is split
/// has a dummy node inserted that contains only an unconditional branch to
/// the block that was originally being targeted.
pub fn split_crit_edges(func: &mut Function, cfg: &ControlFlowGraph) {
    let mut cursor = FuncCursor::over(func);
    let mut critical_edges = Vec::default();

    while let Some(bb) = cursor.next_block() {
        let successors = cursor
            .current_block_terminator_targets()
            .expect("block must have a terminator");

        // critical edge: any edge between a block with multiple successors
        // to a block with multiple predecessors
        if successors.len() <= 1 {
            continue;
        }

        // we know `successors` has more than 1, so any target with multiple predecessors
        // is by definition a critical edge. filter out non-critical edges and mark critical ones
        for critical in successors
            .iter()
            .filter(|target| cfg.n_predecessors(target.block()) > 1)
        {
            critical_edges.push((bb, critical.block()));
        }
    }

    // holds a previous pred and the split associated with it. this is used
    // to enforce a consistent and nice-looking order on our splits, so if one
    // block has multiple required splits they end up in the order they were processed in.
    //
    // (predecessor, previously inserted split block)
    let (mut previous_pred, mut previous_inserted_split) = (Block::reserved(), Block::reserved());

    for (pred, succ) in critical_edges.into_iter() {
        let name = split_block_name(&cursor, pred, succ);

        // if our previous is for the same block, we want to name it based off of the same
        // block (with a different .N suffix) and put it after the previous edge split.
        let insert_after = if previous_pred == pred {
            previous_inserted_split
        } else {
            pred
        };

        let split = cursor.create_block_after(&name, insert_after);

        // update previous for our current iteration
        (previous_pred, previous_inserted_split) = (pred, split);

        // rewrite the branch to be an arg-less branch targeting the split node
        cursor.goto_before(pred);
        let dbg = cursor.inst_debug(cursor.current_block_terminator().unwrap());
        let old = cursor.rewrite_branch_target(succ, BlockWithParams::to(split));

        // split nodes only have unconditional branches containing the arguments that
        // the critical edge used to carry
        cursor.goto_after(split);
        cursor.insert().br(old, dbg);
    }
}

fn split_block_name(cursor: &FuncCursor<'_>, from: Block, to: Block) -> String {
    let strings = cursor.func.ctx().strings();
    let base_name = strings.get(cursor.block_name(from)).unwrap();
    let to_name = strings.get(cursor.block_name(to)).unwrap();

    format!("{base_name}.{to_name}.split_crit_edge")
}
