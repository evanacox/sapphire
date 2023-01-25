//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::analysis::{ControlFlowGraph, ControlFlowGraphAnalysis};
use crate::analysis_preserved;
use crate::arena::SecondaryMap;
use crate::ir::{Block, Cursor, FuncView, Function};
use crate::pass::{FunctionAnalysisManager, FunctionAnalysisPass};
use crate::utility::{IntoTree, SaHashSet};
use smallvec::SmallVec;
use std::any::TypeId;

/// Models the dominator tree for a given control-flow graph. This analysis
/// also gives a reverse postorder for the blocks in the CFG (as this is
/// required for calculating dominators).  
///
/// This implementation stores a tree inside of an arena instead of
/// a naive tree structure, but the rough "dominator tree" structure
/// still exists.
pub struct DominatorTree {
    // maps B -> idom(B) for given block B. "tree" structure comes from going farther
    // up the tree, e.g. tree[idom(b)].
    tree: SecondaryMap<Block, Block>,
    // A valid postorder of the basic blocks in the control-flow graph
    postorder: Vec<Block>,
}

impl DominatorTree {
    /// Computes dominance information for a function.
    pub fn compute(func: &Function, cfg: &ControlFlowGraph) -> Self {
        let po = compute_postorder(func);
        let idoms = compute_idoms(&po, cfg);

        Self {
            tree: idoms,
            postorder: po,
        }
    }

    /// Gets the immediate dominator of `block`, if one exists. The only
    /// block in a given flowgraph that does not have an immediate dominator
    /// is the entry block.
    pub fn idom(&self, block: Block) -> Option<Block> {
        let idom = self.tree[block];

        (idom != block).then_some(idom)
    }

    /// This is equivalent to [`Self::idom`] except in the case where `block`
    /// is the entry node. In that case, `block` is returned.
    pub fn idom_non_strict(&self, block: Block) -> Block {
        self.tree[block]
    }

    /// Checks if `possible_dominator` dominates `block`. Both blocks must actually be in
    /// the given flowgraph.
    ///
    /// This follows the dominance property directly, it returns true if `block` and
    /// `possible_dominator` are the same block. [`Self::strictly_dominates`] does not.
    pub fn dominates(&self, block: Block, possible_dominator: Block) -> bool {
        (block == possible_dominator) || self.strictly_dominates(block, possible_dominator)
    }

    /// Checks if `possible_dominator` strictly `block`. Both blocks must actually be in
    /// the given flowgraph.
    ///
    /// This follows the strict dominance property directly, it returns false if `block` and
    /// `possible_dominator` are the same block. [`Self::strictly_dominates`] does not.
    pub fn strictly_dominates(&self, block: Block, possible_dominator: Block) -> bool {
        let mut curr = block;

        while let Some(block) = self.idom(curr) {
            if block == possible_dominator {
                return true;
            }

            curr = block;
        }

        false
    }

    /// Returns the root (entry) node of the CFG.
    pub fn root(&self) -> Block {
        self.postorder
            .last()
            .copied()
            .expect("should have a root node")
    }

    /// Returns the list of reachable blocks in a valid reverse post-ordering
    /// for the CFG.
    pub fn postorder(&self) -> &[Block] {
        &self.postorder
    }

    /// Returns an iterator over the reachable blocks in reverse postorder.
    pub fn reverse_postorder(&self) -> impl Iterator<Item = Block> + '_ {
        self.postorder().iter().copied().rev()
    }
}

impl IntoTree<'_> for DominatorTree {
    type Node = Block;

    fn root(&self) -> Self::Node {
        self.root()
    }

    fn children(&self, node: Self::Node) -> Vec<Self::Node> {
        let mut result: Vec<Block> = self
            .tree
            .iter()
            .filter(|(from, idom)| **idom == node && *from != node)
            .map(|(block, _)| block)
            .collect();

        result.sort();

        result
    }
}

/// Wrapper analysis that generates a [`DominatorTree`].
pub struct DominatorTreeAnalysis;

impl FunctionAnalysisPass for DominatorTreeAnalysis {
    type Result = DominatorTree;

    fn expects_preserved(&self) -> &'static [TypeId] {
        analysis_preserved!(ControlFlowGraphAnalysis)
    }

    fn run(&mut self, func: &Function, am: &FunctionAnalysisManager) -> Self::Result {
        let cfg = am.get::<ControlFlowGraphAnalysis>(func);

        DominatorTree::compute(func, &cfg)
    }
}

/// Models the dominance frontier information for a function.
pub struct DominanceFrontier {
    //
}

/// Directly computes a valid post-ordering of the blocks in `func`'s
/// control-flow graph.
///
/// This should not be used directly in most cases, you probably want to
/// get this information through [`DominatorTree`] or [`DominatorTreeAnalysis`].
pub fn compute_postorder(func: &Function) -> Vec<Block> {
    let mut po = Vec::new();
    let mut seen = SaHashSet::default();
    let mut cursor = FuncView::over(func);

    // if there are no blocks, the postorder is empty anyway
    if let Some(bb) = cursor.next_block() {
        seen.insert(bb);

        compute_po_recursive(&mut po, &mut seen, &mut cursor);
    }

    po
}

// assumption: current block is `cursor.current_block()`
fn compute_po_recursive(
    order: &mut Vec<Block>,
    seen: &mut SaHashSet<Block>,
    cursor: &mut FuncView<'_>,
) {
    // we change current_block while iterating over the targets
    let curr = cursor.current_block().unwrap();

    // we need to mark it as seen **before** going to any targets, just in case
    // there's any recursive blocks or recursive chains of blocks
    seen.insert(curr);

    // since `current_terminator_targets` returns borrowed data, we can't just iterate inside
    // of an `if let Some(targets) = ... { ... }`. need to copy the data before we deal with it,
    // so we copy the bare minimum we actually need
    let targets: SmallVec<[Block; 4]> = match cursor.current_block_terminator_targets() {
        None => SmallVec::default(),
        Some(targets) => targets //
            .iter()
            .map(|b| b.block())
            .collect(),
    };

    for target in targets {
        // can't use .filter here since that would borrow `seen`
        if !seen.contains(&target) {
            cursor.goto_before(target);

            compute_po_recursive(order, seen, cursor);
        }
    }

    order.push(curr);
}

fn intersect(
    po_numbers: &SecondaryMap<Block, usize>,
    idoms: &SecondaryMap<Block, Block>,
    bb1: Block,
    bb2: Block,
) -> Block {
    let mut f1 = bb1;
    let mut f2 = bb2;

    while f1 != f2 {
        let f2v = po_numbers[f2];

        while po_numbers[f1] < f2v {
            f1 = idoms[f1];
        }

        let f1v = po_numbers[f1];

        while po_numbers[f2] < f1v {
            f2 = idoms[f2];
        }
    }

    f1
}

//
// this implements the dominator algorithm described in "A Simple, Fast Dominance Algorithm"
// by Cooper et. al. See the paper: http://www.hipersoft.rice.edu/grads/publications/dom14.pdf.
//
fn compute_idoms(po: &[Block], cfg: &ControlFlowGraph) -> SecondaryMap<Block, Block> {
    debug_assert!(!po.is_empty());

    // map block -> postorder number.
    // this is just mapping block -> index of block in `po`
    let po_numbers = {
        let mut map = SecondaryMap::default();

        for (i, bb) in po.iter().copied().enumerate() {
            map.insert(bb, i);
        }

        map
    };

    let root = po.last().copied().unwrap();
    let mut idoms = SecondaryMap::default();
    let mut changed = true;

    // for the purposes of the algorithm, the entry node is its own idom
    idoms.insert(root, root);

    while changed {
        // root has no predecessors, so we need to make sure we skip the root node.
        for block in po.iter().rev().copied().skip(1) {
            debug_assert_ne!(block, root);

            let idom = {
                // start by getting every processed predecessor. there will always be at least one
                // when we're iterating in reverse postorder, since the root node was processed at
                // the beginning of the algorithm
                let preds: SmallVec<[Block; 16]> = cfg
                    .predecessors(block)
                    .filter(|p| idoms.contains(*p))
                    .collect();

                // our initial idom is the first in this set of processed preds.
                // order is irrelevant but we have to have one
                let mut iter = preds.into_iter();
                let mut idom = iter.next().expect("every block should have at least one processed predecessor when in reverse postorder");

                // for the rest of our processed preds, perform the "intersect" with `idom`
                for pred in iter {
                    idom = intersect(&po_numbers, &idoms, pred, idom);
                }

                idom
            };

            changed = idoms.insert(block, idom) != Some(idom);
        }
    }

    idoms
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::*;

    #[test]
    fn test_postorder_simple() {
        let mut module = Module::new("test");
        let sig = SigBuilder::new().param(Type::bool()).build();
        let mut b = module.define_function("test", sig);

        //
        // fn void @test(bool) {
        // entry(bool %0):
        //   condbr bool %0, bb1, bb2
        //
        // bb1:
        //   br merge
        //
        // bb2:
        //   br merge
        //
        // merge:
        //   ret void
        // }
        //
        let entry = b.create_block("entry");
        let v0 = b.append_entry_params(entry, DebugInfo::fake())[0];
        let bb1 = b.create_block("bb1");
        let bb2 = b.create_block("bb2");
        let merge = b.create_block("merge");

        b.switch_to(entry);
        b.append().condbr(
            v0,
            BlockWithParams::to(bb1),
            BlockWithParams::to(bb2),
            DebugInfo::fake(),
        );

        b.switch_to(bb1);
        b.append().br(BlockWithParams::to(merge), DebugInfo::fake());

        b.switch_to(bb2);
        b.append().br(BlockWithParams::to(merge), DebugInfo::fake());

        b.switch_to(merge);
        b.append().ret_void(DebugInfo::fake());

        let f = b.define();
        let func = module.function(f);

        let po = compute_postorder(func);

        // while there are two valid postorders for this tree, we know which order
        // the tree is traversed, therefore we can rely on it being one of these
        // orderings (in a test).
        assert_eq!(po, [merge, bb1, bb2, entry]);
    }

    #[test]
    fn test_postorder_irreducible() {
        let mut module = Module::new("test");
        let sig = SigBuilder::new().param(Type::bool()).build();
        let mut b = module.define_function("test", sig);

        //
        // fn void @test(bool) {
        // entry(bool %0):
        //   condbr bool %0, bb1, bb2
        //
        // bb1:
        //   br bb2
        //
        // bb2:
        //   br bb1
        // }
        //
        let entry = b.create_block("entry");
        let v0 = b.append_entry_params(entry, DebugInfo::fake())[0];
        let bb1 = b.create_block("bb1");
        let bb2 = b.create_block("bb2");

        b.switch_to(entry);
        b.append().condbr(
            v0,
            BlockWithParams::to(bb1),
            BlockWithParams::to(bb2),
            DebugInfo::fake(),
        );

        b.switch_to(bb1);
        b.append().br(BlockWithParams::to(bb2), DebugInfo::fake());

        b.switch_to(bb2);
        b.append().br(BlockWithParams::to(bb1), DebugInfo::fake());

        let f = b.define();
        let func = module.function(f);

        let po = compute_postorder(func);

        assert_eq!(po, [bb2, bb1, entry]);
    }

    #[test]
    fn test_postorder_infinite_recurse() {
        let mut module = Module::new("test");
        let sig = SigBuilder::new().param(Type::bool()).build();
        let mut b = module.define_function("test", sig);

        //
        // fn void @test(bool) {
        // entry(bool %0):
        //   br entry(bool %0)
        // }
        //
        let entry = b.create_block("entry");
        let v0 = b.append_entry_params(entry, DebugInfo::fake())[0];

        b.switch_to(entry);
        b.append()
            .br(BlockWithParams::new(entry, &[v0]), DebugInfo::fake());

        let f = b.define();
        let func = module.function(f);

        let po = compute_postorder(func);

        assert_eq!(po, [entry]);
    }

    #[test]
    fn test_domtree_simple() {
        let mut module = Module::new("test");
        let sig_rand = SigBuilder::new().ret(Some(Type::bool())).build();
        let rand = module.declare_function("rand", sig_rand.clone());
        let sig = SigBuilder::new().param(Type::bool()).build();
        let mut b = module.define_function("test", sig);
        let rand_sig = b.import_signature(&sig_rand);

        //
        // fn bool @rand()
        //
        // fn void @test() {
        // one:
        //   %0 = call bool @rand()
        //   condbr bool %0, two, three
        //
        // two:
        //   %1 = call bool @rand()
        //   condbr bool %1, five, nine
        //
        // three:
        //   br four
        //
        // four:
        //   br two
        //
        // five:
        //   %4 = call bool @rand()
        //   condbr bool %4, six, eight
        //
        // six:
        //   %5 = call bool @rand()
        //   condbr bool %5, three, seven
        //
        // seven:
        //   %6 = call bool @rand()
        //   condbr bool %6, one, four
        //
        // eight:
        //   br seven
        //
        // nine:
        //   %7 = call bool @rand()
        //   condbr bool %7, five, eight
        // }
        //
        let one = b.create_block("one");
        let two = b.create_block("two");
        let three = b.create_block("three");
        let four = b.create_block("four");
        let five = b.create_block("five");
        let six = b.create_block("six");
        let seven = b.create_block("seven");
        let eight = b.create_block("eight");
        let nine = b.create_block("nine");

        b.switch_to(one);
        let v0 = b.append().call(rand, rand_sig, &[], DebugInfo::fake());
        let v0 = b.inst_to_result(v0).unwrap();
        b.append().condbr(
            v0,
            BlockWithParams::to(two),
            BlockWithParams::to(three),
            DebugInfo::fake(),
        );

        b.switch_to(two);
        let v1 = b.append().call(rand, rand_sig, &[], DebugInfo::fake());
        let v1 = b.inst_to_result(v1).unwrap();
        b.append().condbr(
            v1,
            BlockWithParams::to(five),
            BlockWithParams::to(nine),
            DebugInfo::fake(),
        );

        b.switch_to(three);
        b.append().br(BlockWithParams::to(four), DebugInfo::fake());

        b.switch_to(four);
        b.append().br(BlockWithParams::to(two), DebugInfo::fake());

        b.switch_to(five);
        b.append().br(BlockWithParams::to(two), DebugInfo::fake());

        b.switch_to(four);
        b.append().br(BlockWithParams::to(two), DebugInfo::fake());

        b.switch_to(five);
        let v2 = b.append().call(rand, rand_sig, &[], DebugInfo::fake());
        let v2 = b.inst_to_result(v2).unwrap();
        b.append().condbr(
            v2,
            BlockWithParams::to(eight),
            BlockWithParams::to(six),
            DebugInfo::fake(),
        );

        b.switch_to(six);
        let v3 = b.append().call(rand, rand_sig, &[], DebugInfo::fake());
        let v3 = b.inst_to_result(v3).unwrap();
        b.append().condbr(
            v3,
            BlockWithParams::to(three),
            BlockWithParams::to(seven),
            DebugInfo::fake(),
        );

        b.switch_to(seven);
        let v4 = b.append().call(rand, rand_sig, &[], DebugInfo::fake());
        let v4 = b.inst_to_result(v4).unwrap();
        b.append().condbr(
            v4,
            BlockWithParams::to(one),
            BlockWithParams::to(four),
            DebugInfo::fake(),
        );

        b.switch_to(eight);
        b.append().br(BlockWithParams::to(seven), DebugInfo::fake());

        b.switch_to(nine);
        let v5 = b.append().call(rand, rand_sig, &[], DebugInfo::fake());
        let v5 = b.inst_to_result(v5).unwrap();
        b.append().condbr(
            v5,
            BlockWithParams::to(five),
            BlockWithParams::to(eight),
            DebugInfo::fake(),
        );

        let f = b.define();
        let func = module.function(f);
        let cfg = ControlFlowGraph::compute(func);
        let domtree = DominatorTree::compute(func, &cfg);

        assert_eq!(domtree.idom(one), None);
        assert_eq!(domtree.idom(two), Some(one));
        assert_eq!(domtree.idom(three), Some(one));
        assert_eq!(domtree.idom(four), Some(one));
        assert_eq!(domtree.idom(five), Some(two));
        assert_eq!(domtree.idom(six), Some(five));
        assert_eq!(domtree.idom(seven), Some(two));
        assert_eq!(domtree.idom(eight), Some(two));
        assert_eq!(domtree.idom(nine), Some(two));

        assert!(domtree.dominates(one, one));
        assert!(domtree.dominates(two, one));
        assert!(domtree.dominates(five, one));
        assert!(domtree.dominates(five, two));
        assert!(domtree.dominates(six, one));
        assert!(domtree.dominates(six, two));
        assert!(domtree.dominates(six, five));

        // same as above, except one doesn't strictly dominate itself
        assert!(!domtree.strictly_dominates(one, one));
        assert!(domtree.strictly_dominates(two, one));
        assert!(domtree.strictly_dominates(five, one));
        assert!(domtree.strictly_dominates(five, two));
        assert!(domtree.strictly_dominates(six, one));
        assert!(domtree.strictly_dominates(six, two));
        assert!(domtree.strictly_dominates(six, five));
    }
}
