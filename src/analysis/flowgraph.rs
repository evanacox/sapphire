//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::ArenaMap;
use crate::dense_arena_key;
use crate::ir::{Block, Cursor, FuncView, Function};
use crate::passes::{FunctionAnalysisManager, FunctionAnalysisPass};
use crate::utility::{SaHashMap, SaHashSet};
use smallvec::SmallVec;
use std::any::TypeId;
use std::collections::hash_map::Entry;

dense_arena_key! {
    struct CFGNode;
}

struct CFGNodeData {
    predecessors: SaHashSet<Block>,
    successors: SaHashSet<Block>,
}

struct CFGComputer<'f> {
    nodes: ArenaMap<CFGNode, CFGNodeData>,
    lookup: SaHashMap<Block, CFGNode>,
    seen: SaHashSet<Block>,
    cursor: FuncView<'f>,
}

impl<'f> CFGComputer<'f> {
    fn new(func: &'f Function) -> Self {
        Self {
            nodes: ArenaMap::default(),
            lookup: SaHashMap::default(),
            seen: SaHashSet::default(),
            cursor: FuncView::over(func),
        }
    }

    fn compute(mut self) -> (ArenaMap<CFGNode, CFGNodeData>, SaHashMap<Block, CFGNode>) {
        while let Some(block) = self.cursor.next_block() {
            self.compute_block(block);
        }

        (self.nodes, self.lookup)
    }

    fn compute_block(&mut self, block: Block) {
        self.cursor.goto_last_inst(block);

        {
            // make sure that any block we compute at least gets
            // an empty node, even if we don't do anything else
            let _ = self.node_of(block);
        }

        let curr = match self.cursor.current_inst() {
            Some(inst) => inst,
            _ => return,
        };

        let successors: SmallVec<[Block; 8]> = match self.cursor.dfg().branch_info(curr) {
            Some([]) => return, // early exit to avoid screwing with vectors unnecessarily
            Some(targets) => SmallVec::from_iter(
                targets //
                    .iter()
                    .map(|target| target.block()),
            ),
            None => panic!("invalid block, did not have a terminator"),
        };

        for successor in successors {
            self.add_edge(block, successor);
        }
    }

    fn add_edge(&mut self, from: Block, to: Block) {
        self.node_of(from).successors.insert(to);
        self.node_of(to).predecessors.insert(from);
    }

    fn node_of(&mut self, block: Block) -> &mut CFGNodeData {
        match self.lookup.entry(block) {
            Entry::Occupied(slot) => &mut self.nodes[*slot.get()],
            Entry::Vacant(slot) => {
                let node = self.nodes.insert(CFGNodeData {
                    predecessors: SaHashSet::default(),
                    successors: SaHashSet::default(),
                });

                slot.insert(node);

                &mut self.nodes[node]
            }
        }
    }
}

/// Models successor/predecessor information about the control-flow graph of
/// a given function.
pub struct ControlFlowGraph {
    nodes: ArenaMap<CFGNode, CFGNodeData>,
    lookup: SaHashMap<Block, CFGNode>,
}

impl ControlFlowGraph {
    /// Directly computes flowgraph information for a given function.
    ///
    /// This should not be used directly in normal compiler passes, this should be
    /// requested from the [`FunctionAnalysisManager`]
    /// through [`CFGAnalysis`].
    pub fn compute(func: &Function) -> Self {
        let computer = CFGComputer::new(func);
        let (nodes, lookup) = computer.compute();

        Self { nodes, lookup }
    }

    /// Returns an iterator over the predecessors for a given block.
    pub fn predecessors(&self, block: Block) -> impl Iterator<Item = Block> + '_ {
        let node = self.data_of(block);

        node.predecessors.iter().copied()
    }

    /// Returns an iterator over the successors for a given block.
    pub fn successors(&self, block: Block) -> impl Iterator<Item = Block> + '_ {
        let node = self.data_of(block);

        node.successors.iter().copied()
    }

    /// Checks if a given block `pred` is a predecessor of `block`
    pub fn is_pred_of(&self, block: Block, pred: Block) -> bool {
        let node = self.data_of(block);

        node.predecessors.contains(&pred)
    }

    /// Checks if a given block `pred` is a successor of `block`
    pub fn is_succ_of(&self, block: Block, succ: Block) -> bool {
        let node = self.data_of(block);

        node.successors.contains(&succ)
    }

    fn data_of(&self, block: Block) -> &CFGNodeData {
        let idx = self.lookup[&block];

        &self.nodes[idx]
    }
}

/// An analysis pass that wraps up a [`ControlFlowGraph`] into
/// something that can actually be used inside of transform passes.
pub struct CFGAnalysis;

impl FunctionAnalysisPass for CFGAnalysis {
    type Result = ControlFlowGraph;

    fn expects_preserved(&self) -> &'static [TypeId] {
        &[]
    }

    fn run(&mut self, func: &Function, _: &FunctionAnalysisManager) -> Self::Result {
        ControlFlowGraph::compute(func)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::*;
    use std::iter;

    #[test]
    fn no_blocks() {
        let mut m = Module::new("test");
        let sig = SigBuilder::new().build();
        let b = m.define_function("main", sig);
        let f = b.define();

        // shouldn't panic
        let _ = ControlFlowGraph::compute(m.function(f));
    }

    #[test]
    fn one_block() {
        let mut m = Module::new("test");
        let sig = SigBuilder::new().build();
        let mut b = m.define_function("main", sig);

        // fn void @main() {
        // entry:
        //   unreachable
        // }
        let entry = b.create_block("entry");
        b.switch_to(entry);
        b.append().unreachable(DebugInfo::fake());

        let f = b.define();
        let cfg = ControlFlowGraph::compute(m.function(f));

        assert_eq!(cfg.predecessors(entry).next(), None);
    }

    #[test]
    fn merge() {
        let mut m = Module::new("test");
        let sig = SigBuilder::new().param(Type::bool()).build();
        let mut b = m.define_function("main", sig);

        //
        // fn void @main(bool) {
        // entry(bool %0):
        //   condbr bool %0, if, else
        //
        // if.true:
        //   br merge
        //
        // otherwise:
        //   br merge
        //
        // merge:
        //   ret void
        // }
        //
        let entry = b.create_block("entry");
        let entry_params = b.append_entry_params(entry, DebugInfo::fake());
        let if_true = b.create_block("if.true");
        let otherwise = b.create_block("otherwise");
        let merge = b.create_block("merge");

        b.switch_to(entry);
        b.append().condbr(
            entry_params[0],
            BlockWithParams::new(if_true, &[]),
            BlockWithParams::new(otherwise, &[]),
            DebugInfo::fake(),
        );

        b.switch_to(if_true);
        b.append()
            .br(BlockWithParams::new(merge, &[]), DebugInfo::fake());

        b.switch_to(otherwise);
        b.append()
            .br(BlockWithParams::new(merge, &[]), DebugInfo::fake());

        b.switch_to(merge);
        b.append().ret_void(DebugInfo::fake());

        let f = b.define();
        let cfg = ControlFlowGraph::compute(m.function(f));

        assert_eq!(cfg.predecessors(entry).next(), None);
        assert!(cfg.is_pred_of(if_true, entry));
        assert!(cfg.is_pred_of(otherwise, entry));
        assert!(cfg.is_pred_of(merge, if_true));
        assert!(cfg.is_pred_of(merge, otherwise));
        assert!(cfg.is_succ_of(entry, if_true));
        assert!(cfg.is_succ_of(entry, otherwise));
        assert!(cfg.successors(if_true).eq(iter::once(merge)));
        assert!(cfg.successors(otherwise).eq(iter::once(merge)));
        assert_eq!(cfg.successors(merge).next(), None);
    }

    #[test]
    fn infinite_loop() {
        let mut m = Module::new("test");
        let sig = SigBuilder::new().build();
        let mut b = m.define_function("main", sig);

        //
        // fn void @main() {
        // entry:
        //   br entry
        // }
        //
        let entry = b.create_block("entry");
        b.switch_to(entry);
        b.append()
            .br(BlockWithParams::new(entry, &[]), DebugInfo::fake());

        let f = b.define();
        let cfg = ControlFlowGraph::compute(m.function(f));

        assert!(cfg.predecessors(entry).eq(iter::once(entry)));
        assert!(cfg.successors(entry).eq(iter::once(entry)));
    }

    #[test]
    fn unreachable_block() {
        let mut m = Module::new("test");
        let sig = SigBuilder::new().build();
        let mut b = m.define_function("main", sig);

        //
        // fn void @main() {
        // entry:
        //   br entry
        //
        // unreachable.block:
        //   unreachable
        // }
        //
        let entry = b.create_block("entry");
        let unreachable_block = b.create_block("unreachable.block");
        b.switch_to(entry);
        b.append()
            .br(BlockWithParams::new(entry, &[]), DebugInfo::fake());

        b.switch_to(unreachable_block);
        b.append().unreachable(DebugInfo::fake());

        let f = b.define();
        let cfg = ControlFlowGraph::compute(m.function(f));

        assert!(cfg.predecessors(entry).eq(iter::once(entry)));
        assert!(cfg.successors(entry).eq(iter::once(entry)));
        assert_eq!(cfg.predecessors(unreachable_block).next(), None);
        assert_eq!(cfg.successors(unreachable_block).next(), None);
    }

    #[test]
    fn canonical_loop() {
        let mut m = Module::new("test");
        let sig = SigBuilder::new()
            .ret(Some(Type::i32()))
            .params(&[Type::i32(), Type::ptr()])
            .build();

        let mut b = m.define_function("main", sig);

        //
        // fn void @main() {
        // entry:
        //   %0 = bconst bool true
        //   br loop.head(bool %0)
        //
        // loop.head(bool %1):
        //   condbr bool %1, loop.body, exit
        //
        // loop.body:
        //   br loop.latch
        //
        // loop.latch:
        //   %2 = bconst bool false
        //   br loop.head(bool %2)
        //
        // exit:
        //   ret void
        // }
        //
        let entry = b.create_block("entry");
        let loop_head = b.create_block("loop.head");
        let loop_body = b.create_block("loop.body");
        let loop_latch = b.create_block("loop.latch");
        let exit = b.create_block("exit");

        // in block so I can collapse this in editor
        {
            let v1 = b.append_block_param(loop_head, Type::bool(), DebugInfo::fake());

            b.switch_to(entry);

            let v0 = b.append().bconst(true, DebugInfo::fake());
            b.append()
                .br(BlockWithParams::new(loop_head, &[v0]), DebugInfo::fake());

            b.switch_to(loop_head);
            b.append().condbr(
                v1,
                BlockWithParams::new(loop_body, &[]),
                BlockWithParams::new(exit, &[]),
                DebugInfo::fake(),
            );

            b.switch_to(loop_body);
            b.append()
                .br(BlockWithParams::new(loop_latch, &[]), DebugInfo::fake());

            b.switch_to(loop_latch);
            let v2 = b.append().bconst(false, DebugInfo::fake());
            b.append()
                .br(BlockWithParams::new(loop_head, &[v2]), DebugInfo::fake());

            b.switch_to(exit);
            b.append().ret_void(DebugInfo::fake());
        }

        let f = b.define();
        let cfg = ControlFlowGraph::compute(m.function(f));

        assert_eq!(cfg.predecessors(entry).next(), None);
        assert!(cfg.successors(entry).eq(iter::once(loop_head)));

        let loop_head_predecessors = cfg.predecessors(loop_head).collect::<Vec<_>>();
        let loop_head_successors = cfg.successors(loop_head).collect::<Vec<_>>();
        assert!(loop_head_predecessors.contains(&entry));
        assert!(loop_head_predecessors.contains(&loop_latch));
        assert!(loop_head_successors.contains(&loop_body));
        assert!(loop_head_successors.contains(&exit));

        assert!(cfg.predecessors(loop_body).eq(iter::once(loop_head)));
        assert!(cfg.successors(loop_body).eq(iter::once(loop_latch)));

        assert!(cfg.predecessors(loop_latch).eq(iter::once(loop_body)));
        assert!(cfg.successors(loop_latch).eq(iter::once(loop_head)));

        assert!(cfg.predecessors(exit).eq(iter::once(loop_head)));
        assert_eq!(cfg.successors(exit).next(), None);
    }

    #[test]
    fn irreducible() {
        let mut m = Module::new("test");
        let sig = SigBuilder::new().build();
        let mut b = m.define_function("main", sig);

        //
        // fn void @main() {
        // entry:
        //   br a
        //
        // a:
        //   br b
        //
        // b:
        //   br a
        // }
        //
        let entry = b.create_block("entry");
        let block_a = b.create_block("a");
        let block_b = b.create_block("b");
        b.switch_to(entry);
        b.append()
            .br(BlockWithParams::new(block_a, &[]), DebugInfo::fake());

        b.switch_to(block_a);
        b.append()
            .br(BlockWithParams::new(block_b, &[]), DebugInfo::fake());

        b.switch_to(block_b);
        b.append()
            .br(BlockWithParams::new(block_a, &[]), DebugInfo::fake());

        let f = b.define();
        let cfg = ControlFlowGraph::compute(m.function(f));

        assert_eq!(cfg.predecessors(entry).next(), None);
        assert!(cfg.successors(entry).eq(iter::once(block_a)));

        let block_a_preds = cfg.predecessors(block_a).collect::<Vec<_>>();
        assert!(block_a_preds.contains(&entry));
        assert!(block_a_preds.contains(&block_b));
        assert!(cfg.successors(block_a).eq(iter::once(block_b)));

        assert!(cfg.predecessors(block_b).eq(iter::once(block_a)));
        assert!(cfg.successors(block_b).eq(iter::once(block_a)));
    }
}
