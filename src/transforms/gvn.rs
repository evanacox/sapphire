//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::{DominatorTree, DominatorTreeAnalysis};
use crate::ir::{Block, Cursor, CursorMut, FuncCursor, Function};
use crate::pass::{FunctionAnalysisManager, FunctionTransformPass, PreservedAnalyses};
use crate::transforms::common::has_side_effect;
use crate::utility::SaHashMap;
use smallvec::SmallVec;
use std::hash::Hash;

/// A simple GVN (global value numbering) pass.
///
/// This pass works best when the code is already canonicalized
/// and isn't full of memory operations, so it would be a good idea to
/// run `mem2reg`, `dce` and `simplifyinst` before this pass.
pub struct GlobalValueNumberingPass;

impl FunctionTransformPass for GlobalValueNumberingPass {
    fn run(&mut self, func: &mut Function, am: &mut FunctionAnalysisManager) -> PreservedAnalyses {
        gvn(func, &am.get::<DominatorTreeAnalysis>(func));

        PreservedAnalyses::all()
    }
}

/// Runs a global value-numbering algorithm over `func` to remove redundant
/// expressions.
///
/// This pass works best
pub fn gvn(func: &mut Function, domtree: &DominatorTree) {
    let mut tables = ScopedHashMap::new();
    let mut scope_stack = SmallVec::<[Block; 16]>::new();
    let mut cursor = FuncCursor::over(func);

    for bb in domtree.reverse_postorder() {
        // since we aren't directly dfs-ing the dominator tree, we need to keep track of
        // the stack of scopes at any given point and then leave any scopes once
        // we hit a point where the previous scope didn't dominate us.
        while let Some(prev) = scope_stack.last().copied() {
            if domtree.dominates(bb, prev) {
                break;
            }

            scope_stack.pop();
            tables.leave_scope();
        }

        cursor.goto_before(bb);
        scope_stack.push(bb);
        tables.enter_scope();

        while let Some(inst) = cursor.next_inst() {
            if has_side_effect(cursor.dfg(), inst) {
                continue;
            }

            // the instructions that have weird data impls (i.e. own heap allocations or
            // whatever) are covered by `has_side_effect` and thus won't affect this
            let data = cursor.inst_data(inst).clone();
            let result = cursor
                .inst_to_result(inst)
                .expect("instruction without result should have side effect");

            match tables.closest(&data) {
                Some(original) => {
                    cursor.replace_uses_with(result, original);
                    cursor.remove_inst_and_move_back();
                }
                None => {
                    tables.insert(data, result);
                }
            }
        }
    }
}

#[derive(Debug, Clone)]
struct ScopedHashMap<K, V> {
    inner: Vec<SaHashMap<K, V>>,
}

impl<K, V> ScopedHashMap<K, V>
where
    K: Hash + Eq,
    V: Copy,
{
    fn new() -> Self {
        Self {
            inner: Vec::default(),
        }
    }

    fn enter_scope(&mut self) {
        self.inner.push(SaHashMap::default());
    }

    fn leave_scope(&mut self) {
        self.inner.pop();
    }

    fn insert(&mut self, key: K, value: V) {
        self.inner
            .last_mut()
            .expect("cannot insert without a scope")
            .insert(key, value);
    }

    fn closest(&self, key: &K) -> Option<V> {
        for scope in self.inner.iter().rev() {
            if let Some(val) = scope.get(key) {
                return Some(*val);
            }
        }

        None
    }
}
