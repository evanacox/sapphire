//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::ControlFlowGraph;
use crate::ir::*;
use crate::utility::Packable;
use smallvec::SmallVec;
use std::iter;

/// Removes a parameter from a block and rewrites all branches to that block to not include
/// that parameter.
///
/// Effectively, it transforms this:
/// ```none
///   br a(i32 %0)
///
/// a(i32 %1):
///   ; ...
/// ```
/// into this:
/// ```none
///   br a
///
/// a:
///   ; ...
/// ```
pub fn rewrite_and_remove_block_param(
    cursor: &mut FuncCursor<'_>,
    cfg: &ControlFlowGraph,
    block: Block,
    param: Value,
) {
    let idx = match cursor.value_def(param) {
        ValueDef::Param(bb, idx) => {
            debug_assert_eq!(bb, block);

            idx
        }
        _ => unreachable!("tried to rewrite value that wasn't a block param"),
    };

    let mut new_params = SmallVec::<[Value; 16]>::new();

    // every pred has to jump to this somehow, if it's valid it passed the block parma with it.
    for pred in cfg.predecessors(block) {
        let branch = cursor
            .layout()
            .block_last_inst(pred)
            .expect("pred data is stale, block is empty");

        let args = cursor
            .dfg()
            .branch_info(branch)
            .expect("last inst isn't a terminator")
            .iter()
            .find(|target| target.block() == block)
            .expect("pred data is stale, block doesn't branch to successor");

        for (i, arg) in args.args().iter().enumerate() {
            if i != idx as usize {
                new_params.push(*arg);
            }
        }

        cursor.rewrite_branch_args(branch, block, &new_params);

        new_params.clear();
    }

    cursor.remove_block_param(block, param);
}

/// Rewrites a branch target to replace an argument with another.
///
/// If the target does not have that many arguments, fake padding values (`Value::reserved`)
/// are inserted to fill in the gaps with the expectation they will be inserted later.
///
/// This is to remove any order dependence in passes that need to do this (like `mem2reg`).
pub fn rewrite_pad_branch_argument(
    cursor: &mut FuncCursor<'_>,
    branch: Inst,
    branch_to: Block,
    param: usize,
    new: Value,
) {
    for target in cursor.branch_info(branch).unwrap() {
        if target.block() == branch_to {
            let got = target.args().len();
            let expected = cursor.block_params(branch_to).len();

            // if we have the correct number of arguments, we just need to replace
            // the argument. if we don't we rewrite it with some fake values
            // that can be replaced later
            if got == expected {
                cursor.replace_branch_arg(branch, branch_to, param, new)
            } else {
                let mut items = SmallVec::<[Value; 16]>::default();

                items.extend_from_slice(target.args());
                items.insert_many(
                    items.len(),
                    iter::repeat(Value::reserved()).take(param - items.len()),
                );

                items.push(new);

                cursor.rewrite_branch_args(branch, branch_to, &items);
            }

            return;
        }
    }
}
