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
use crate::analysis_preserved;
use crate::arena::SecondaryMap;
use crate::ir::{Block, Cursor, FuncView, Function};
use crate::pass::{FunctionAnalysisManager, FunctionAnalysisPass};
use crate::utility::{IntoTree, Packable, SaHashSet};
use smallvec::SmallVec;
use std::any::TypeId;
use std::iter;

/// Models the dominator tree for a given control-flow graph. This analysis
/// also gives a reverse postorder for the blocks in the CFG (as this is
/// required for calculating dominators, and is useful information for
/// other passes to have as well).
///
/// # Implementation
/// The algorithm used is described in "A Simple, Fast Dominance Algorithm"
/// by Cooper et. al.
///
/// This implementation stores a tree inside of an arena instead of
/// a direct tree with separately allocated nodes, but the rough
/// "dominator tree" structure still exists.
pub struct DominatorTree {
    // maps B -> idom(B) for given block B. "tree" structure comes from going farther
    // up the tree, e.g. tree[idom(b)].
    tree: SecondaryMap<Block, Block>,
    // A valid postorder of the basic blocks in the control-flow graph.
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

        if idom.is_reserved() {
            None
        } else {
            Some(idom)
        }
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

    /// Walks over the **dominator tree** in DFS preorder. This is only
    /// here for use in the `mem2reg` pass right now (as this is required
    /// for the correctness of the renaming algorithm).
    pub fn compute_tree_dfs_preorder(&self) -> Vec<Block> {
        compute_domtree_dfs_preorder(self.root(), &self.tree)
    }

    /// Checks if a block is reachable from the entry node
    pub fn is_reachable(&self, block: Block) -> bool {
        self.tree.contains(block)
    }
}

impl IntoTree<'_> for DominatorTree {
    type Node = Block;

    fn root(&self) -> Self::Node {
        self.root()
    }

    fn children(&self, node: Self::Node) -> SmallVec<[Self::Node; 12]> {
        let mut result: SmallVec<[Block; 12]> = self
            .tree
            .iter()
            .filter(|(_, idom)| **idom == node)
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
///
/// Note that this implementation only models dominance frontier info for the reachable
/// nodes in the graph.
///
/// The dominance frontier effectively models the "join points" of the program,
/// a block's dominance frontier is the set of nodes directly outside of the
/// region that a block dominates.
///
/// Formally, for a given basic block A, the dominance frontier is the set
/// of nodes B where A does not dominate B, but B dominates an immediate
/// predecessor of A.
///
/// See <https://en.wikipedia.org/wiki/Static_single-assignment_form#Computing_minimal_SSA_using_dominance_frontiers>
pub struct DominanceFrontier {
    frontier: SecondaryMap<Block, Vec<Block>>,
}

impl DominanceFrontier {
    /// Computes the dominance frontier of a given control-flow graph.
    ///
    /// The dominance frontier relies on the dominance information in
    /// `domtree`, and only contains the nodes that were reachable from
    /// the entry node.
    pub fn compute(cfg: &ControlFlowGraph, domtree: &DominatorTree) -> Self {
        //
        // the algorithm used is the dominance frontier algorithm described
        // in "A Simple, Fast Dominance Algorithm" by Cooper et. al. See
        // the paper: http://www.hipersoft.rice.edu/grads/publications/dom14.pdf.
        //
        let mut frontier = SecondaryMap::default();

        // we just need every reachable node, this algorithm doesn't specifically
        // need postorder traversal.
        for node in domtree.postorder() {
            frontier.insert(*node, Vec::default());
        }

        for node in domtree.postorder() {
            let mut preds = cfg.predecessors(*node);
            let (one, two) = (preds.next(), preds.next());

            // if we take the first two elements and the second is Some(..), we have
            // multiple predecessors. we can't necessarily trust size_hint for
            // the correctness of the algorithm
            if let (Some(one), Some(two)) = (one, two) {
                // we need to filter out any unreachable blocks that may be preds here, consider:
                //
                // entry:
                //   br a
                // a:
                //   br c
                // b:
                //   br c
                // c:
                //   a and b are preds, only a is reachable
                for pred in iter::once(one) // I apologize
                    .chain(iter::once(two))
                    .chain(preds)
                    .filter(|pred| domtree.is_reachable(*pred))
                {
                    let mut runner = pred;

                    while runner != domtree.idom(*node).unwrap() {
                        let v = &mut frontier[runner];

                        // these arrays are almost always very small, this is fine.
                        // makes it easier to deal with the frontier in other code,
                        // for now that seems to be worth the trade-off
                        if !v.contains(node) {
                            v.push(*node);
                        }

                        runner = domtree.idom(runner).unwrap();
                    }
                }
            }
        }

        Self { frontier }
    }

    /// Gets the blocks in the dominance frontier of `block`.
    ///
    /// These are the blocks "one past the edge" of `block`'s range
    /// of dominance.
    pub fn frontier(&self, block: Block) -> &[Block] {
        &self.frontier[block]
    }
}

/// Wrapper analysis that generates a [`DominanceFrontier`].
pub struct DominanceFrontierAnalysis;

impl FunctionAnalysisPass for DominanceFrontierAnalysis {
    type Result = DominanceFrontier;

    fn expects_preserved(&self) -> &'static [TypeId] {
        analysis_preserved!(ControlFlowGraphAnalysis)
    }

    fn run(&mut self, func: &Function, am: &FunctionAnalysisManager) -> Self::Result {
        let cfg = am.get::<ControlFlowGraphAnalysis>(func);
        let domtree = am.get::<DominatorTreeAnalysis>(func);

        DominanceFrontier::compute(&cfg, &domtree)
    }
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

fn compute_domtree_dfs_preorder(root: Block, tree: &SecondaryMap<Block, Block>) -> Vec<Block> {
    let mut out = Vec::default();

    compute_domtree_dfs_preorder_recursive(root, tree, &mut out);

    out
}

fn compute_domtree_dfs_preorder_recursive(
    curr: Block,
    tree: &SecondaryMap<Block, Block>,
    out: &mut Vec<Block>,
) {
    out.push(curr);

    // unfortunately we optimize for the child -> idom case, not the idom -> child case.
    // in most situations this is a good call, but here it is not
    for (child, _) in tree.iter().filter(|(_, idom)| **idom == curr) {
        compute_domtree_dfs_preorder_recursive(child, tree, out);
    }
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
        changed = false;

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

    // remove the root -> root idom relationship, mark a
    // sentinel we can look for instead.
    idoms.insert(root, Block::reserved());

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

    #[test]
    fn test_domtree_two() {
        let mut module = Module::new("test");
        let sig_rand = SigBuilder::new().ret(Some(Type::bool())).build();
        let rand = module.declare_function("rand", sig_rand.clone());
        let sig = SigBuilder::new().param(Type::bool()).build();
        let mut b = module.define_function("main", sig);
        let rand_sig = b.import_signature(&sig_rand);

        // fn bool @rand()
        //
        // fn void @main() {
        // bb0:
        //     %0 = call bool @rand()
        //     br bb1
        //
        // bb1:
        //     condbr bool %0, bb2, bb5
        //
        // bb2:
        //     br bb3
        //
        // bb3:
        //     condbr bool %0, bb4, bb1
        //
        // bb4:
        //     ret void
        //
        // bb5:
        //     condbr bool %0, bb6, bb8
        //
        // bb6:
        //     br bb7
        //
        // bb7:
        //     br bb3
        //
        // bb8:
        //     br bb7
        // }
        let bb0 = b.create_block("bb0");
        let bb1 = b.create_block("bb1");
        let bb2 = b.create_block("bb2");
        let bb3 = b.create_block("bb3");
        let bb4 = b.create_block("bb4");
        let bb5 = b.create_block("bb5");
        let bb6 = b.create_block("bb6");
        let bb7 = b.create_block("bb7");
        let bb8 = b.create_block("bb8");

        b.switch_to(bb0);
        let v0 = b.append().call(rand, rand_sig, &[], DebugInfo::fake());
        let v0 = b.inst_to_result(v0).unwrap();
        b.append().br(BlockWithParams::to(bb1), DebugInfo::fake());

        b.switch_to(bb1);
        b.append().condbr(
            v0,
            BlockWithParams::to(bb2),
            BlockWithParams::to(bb5),
            DebugInfo::fake(),
        );

        b.switch_to(bb2);
        b.append().br(BlockWithParams::to(bb3), DebugInfo::fake());

        b.switch_to(bb3);
        b.append().condbr(
            v0,
            BlockWithParams::to(bb4),
            BlockWithParams::to(bb1),
            DebugInfo::fake(),
        );

        b.switch_to(bb4);
        b.append().ret_void(DebugInfo::fake());

        b.switch_to(bb5);
        b.append().condbr(
            v0,
            BlockWithParams::to(bb6),
            BlockWithParams::to(bb8),
            DebugInfo::fake(),
        );

        b.switch_to(bb6);
        b.append().br(BlockWithParams::to(bb7), DebugInfo::fake());

        b.switch_to(bb7);
        b.append().br(BlockWithParams::to(bb3), DebugInfo::fake());

        b.switch_to(bb8);
        b.append().br(BlockWithParams::to(bb7), DebugInfo::fake());

        let func = b.define();
        let main = module.function(func);

        let cfg = ControlFlowGraph::compute(main);
        let domtree = DominatorTree::compute(main, &cfg);

        // bb0 dom = { bb0 }
        assert!(domtree.dominates(bb0, bb0));

        // bb1 dom = { bb0, bb1 }
        assert!(domtree.dominates(bb1, bb0));
        assert!(domtree.dominates(bb1, bb1));

        // bb2 dom = { bb0, bb1, bb2 }
        assert!(domtree.dominates(bb2, bb0));
        assert!(domtree.dominates(bb2, bb1));
        assert!(domtree.dominates(bb2, bb2));

        // bb3 dom = { bb0, bb1, bb3 }
        assert!(domtree.dominates(bb3, bb0));
        assert!(domtree.dominates(bb3, bb1));
        assert!(domtree.dominates(bb3, bb3));

        // bb4 dom = { bb0, bb1, bb3, bb4 }
        assert!(domtree.dominates(bb4, bb0));
        assert!(domtree.dominates(bb4, bb1));
        assert!(domtree.dominates(bb4, bb3));
        assert!(domtree.dominates(bb4, bb4));

        // bb5 dom = { bb0, bb1, bb5 }
        assert!(domtree.dominates(bb5, bb0));
        assert!(domtree.dominates(bb5, bb1));
        assert!(domtree.dominates(bb5, bb5));

        // bb6 dom = { bb0, bb1, bb5, bb6 }
        assert!(domtree.dominates(bb6, bb0));
        assert!(domtree.dominates(bb6, bb1));
        assert!(domtree.dominates(bb6, bb5));
        assert!(domtree.dominates(bb6, bb6));

        // bb7 dom = { bb0, bb1, bb5, bb7 }
        assert!(domtree.dominates(bb7, bb0));
        assert!(domtree.dominates(bb7, bb1));
        assert!(domtree.dominates(bb7, bb5));
        assert!(domtree.dominates(bb7, bb7));

        // bb8 dom = { bb0, bb1, bb5, bb8 }
        assert!(domtree.dominates(bb8, bb0));
        assert!(domtree.dominates(bb8, bb1));
        assert!(domtree.dominates(bb8, bb5));
        assert!(domtree.dominates(bb8, bb8));

        // bb0 dom = { bb0 }
        assert!(!domtree.strictly_dominates(bb0, bb0));

        // bb1 dom = { bb0, bb1 }
        assert!(domtree.strictly_dominates(bb1, bb0));
        assert!(!domtree.strictly_dominates(bb1, bb1));

        // bb2 dom = { bb0, bb1, bb2 }
        assert!(domtree.strictly_dominates(bb2, bb0));
        assert!(domtree.strictly_dominates(bb2, bb1));
        assert!(!domtree.strictly_dominates(bb2, bb2));

        // bb3 dom = { bb0, bb1, bb3 }
        assert!(domtree.strictly_dominates(bb3, bb0));
        assert!(domtree.strictly_dominates(bb3, bb1));
        assert!(!domtree.strictly_dominates(bb3, bb3));

        // bb4 dom = { bb0, bb1, bb3, bb4 }
        assert!(domtree.strictly_dominates(bb4, bb0));
        assert!(domtree.strictly_dominates(bb4, bb1));
        assert!(domtree.strictly_dominates(bb4, bb3));
        assert!(!domtree.strictly_dominates(bb4, bb4));

        // bb5 dom = { bb0, bb1, bb5 }
        assert!(domtree.strictly_dominates(bb5, bb0));
        assert!(domtree.strictly_dominates(bb5, bb1));
        assert!(!domtree.strictly_dominates(bb5, bb5));

        // bb6 dom = { bb0, bb1, bb5, bb6 }
        assert!(domtree.strictly_dominates(bb6, bb0));
        assert!(domtree.strictly_dominates(bb6, bb1));
        assert!(domtree.strictly_dominates(bb6, bb5));
        assert!(!domtree.strictly_dominates(bb6, bb6));

        // bb7 dom = { bb0, bb1, bb5, bb7 }
        assert!(domtree.strictly_dominates(bb7, bb0));
        assert!(domtree.strictly_dominates(bb7, bb1));
        assert!(domtree.strictly_dominates(bb7, bb5));
        assert!(!domtree.strictly_dominates(bb7, bb7));

        // bb8 dom = { bb0, bb1, bb5, bb8 }
        assert!(domtree.strictly_dominates(bb8, bb0));
        assert!(domtree.strictly_dominates(bb8, bb1));
        assert!(domtree.strictly_dominates(bb8, bb5));
        assert!(!domtree.strictly_dominates(bb8, bb8));
    }

    #[test]
    fn test_dominance_frontier() {
        let mut module = Module::new("test");
        let sig_rand = SigBuilder::new().ret(Some(Type::bool())).build();
        let rand = module.declare_function("rand", sig_rand.clone());
        let sig = SigBuilder::new().param(Type::bool()).build();
        let mut b = module.define_function("main", sig);
        let rand_sig = b.import_signature(&sig_rand);

        // fn bool @rand()
        //
        // fn void @main() {
        // bb0:
        //     %0 = call bool @rand()
        //     br bb1
        //
        // bb1:
        //     condbr bool %0, bb2, bb5
        //
        // bb2:
        //     br bb3
        //
        // bb3:
        //     condbr bool %0, bb4, bb1
        //
        // bb4:
        //     ret void
        //
        // bb5:
        //     condbr bool %0, bb6, bb8
        //
        // bb6:
        //     br bb7
        //
        // bb7:
        //     br bb3
        //
        // bb8:
        //     br bb7
        // }
        let bb0 = b.create_block("bb0");
        let bb1 = b.create_block("bb1");
        let bb2 = b.create_block("bb2");
        let bb3 = b.create_block("bb3");
        let bb4 = b.create_block("bb4");
        let bb5 = b.create_block("bb5");
        let bb6 = b.create_block("bb6");
        let bb7 = b.create_block("bb7");
        let bb8 = b.create_block("bb8");

        b.switch_to(bb0);
        let v0 = b.append().call(rand, rand_sig, &[], DebugInfo::fake());
        let v0 = b.inst_to_result(v0).unwrap();
        b.append().br(BlockWithParams::to(bb1), DebugInfo::fake());

        b.switch_to(bb1);
        b.append().condbr(
            v0,
            BlockWithParams::to(bb2),
            BlockWithParams::to(bb5),
            DebugInfo::fake(),
        );

        b.switch_to(bb2);
        b.append().br(BlockWithParams::to(bb3), DebugInfo::fake());

        b.switch_to(bb3);
        b.append().condbr(
            v0,
            BlockWithParams::to(bb4),
            BlockWithParams::to(bb1),
            DebugInfo::fake(),
        );

        b.switch_to(bb4);
        b.append().ret_void(DebugInfo::fake());

        b.switch_to(bb5);
        b.append().condbr(
            v0,
            BlockWithParams::to(bb6),
            BlockWithParams::to(bb8),
            DebugInfo::fake(),
        );

        b.switch_to(bb6);
        b.append().br(BlockWithParams::to(bb7), DebugInfo::fake());

        b.switch_to(bb7);
        b.append().br(BlockWithParams::to(bb3), DebugInfo::fake());

        b.switch_to(bb8);
        b.append().br(BlockWithParams::to(bb7), DebugInfo::fake());

        let func = b.define();
        let main = module.function(func);

        let cfg = ControlFlowGraph::compute(main);
        let domtree = DominatorTree::compute(main, &cfg);
        let df = DominanceFrontier::compute(&cfg, &domtree);

        assert_eq!(df.frontier(bb0), &[]);
        assert_eq!(df.frontier(bb1), &[bb1]);
        assert_eq!(df.frontier(bb2), &[bb3]);
        assert_eq!(df.frontier(bb3), &[bb1]);
        assert_eq!(df.frontier(bb4), &[]);
        assert_eq!(df.frontier(bb5), &[bb3]);
        assert_eq!(df.frontier(bb6), &[bb7]);
        assert_eq!(df.frontier(bb7), &[bb3]);
        assert_eq!(df.frontier(bb8), &[bb7]);
    }

    #[test]
    fn test_dominance_frontier2() {
        let mut module = Module::new("test");
        let sig_rand = SigBuilder::new().ret(Some(Type::bool())).build();
        let rand = module.declare_function("rand", sig_rand.clone());
        let sig = SigBuilder::new().param(Type::bool()).build();
        let mut b = module.define_function("main", sig);
        let rand_sig = b.import_signature(&sig_rand);

        // fn bool @rand()
        //
        // fn void @main() {
        // r:
        //     %0 = call bool @rand()
        //     br a
        //
        // a:
        //     condbr bool %0, b, c
        //
        // b:
        //     br d
        //
        // c:
        //     condbr bool %0, d, e
        //
        // d:
        //     condbr bool %0, a, e
        //
        // e:
        //     ret void
        // }
        let bbr = b.create_block("r");
        let bba = b.create_block("a");
        let bbb = b.create_block("b");
        let bbc = b.create_block("c");
        let bbd = b.create_block("d");
        let bbe = b.create_block("e");

        b.switch_to(bbr);
        let v0 = b.append().call(rand, rand_sig, &[], DebugInfo::fake());
        let v0 = b.inst_to_result(v0).unwrap();
        b.append().br(BlockWithParams::to(bba), DebugInfo::fake());

        b.switch_to(bba);
        b.append().condbr(
            v0,
            BlockWithParams::to(bbb),
            BlockWithParams::to(bbc),
            DebugInfo::fake(),
        );

        b.switch_to(bbb);
        b.append().br(BlockWithParams::to(bbd), DebugInfo::fake());

        b.switch_to(bbc);
        b.append().condbr(
            v0,
            BlockWithParams::to(bbd),
            BlockWithParams::to(bbe),
            DebugInfo::fake(),
        );

        b.switch_to(bbd);
        b.append().condbr(
            v0,
            BlockWithParams::to(bba),
            BlockWithParams::to(bbe),
            DebugInfo::fake(),
        );

        b.switch_to(bbe);
        b.append().ret_void(DebugInfo::fake());

        let func = b.define();
        let main = module.function(func);

        let cfg = ControlFlowGraph::compute(main);
        let domtree = DominatorTree::compute(main, &cfg);
        let df = DominanceFrontier::compute(&cfg, &domtree);

        let mut bbc_df: Vec<Block> = df.frontier(bbc).to_vec();
        let mut bbd_df: Vec<Block> = df.frontier(bbd).to_vec();

        bbc_df.sort();
        bbd_df.sort();

        assert_eq!(df.frontier(bbr), &[]);
        assert_eq!(df.frontier(bba), &[bba]);
        assert_eq!(df.frontier(bbb), &[bbd]);
        assert_eq!(&bbc_df, &[bbd, bbe]);
        assert_eq!(&bbd_df, &[bba, bbe]);
        assert_eq!(df.frontier(bbe), &[]);
    }
}
