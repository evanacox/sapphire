//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::SecondaryMap;
use crate::ir::{Block, Inst};
use crate::utility::PackedOption;
use std::fmt;
use std::fmt::{Debug, Formatter};

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
struct InstNode {
    prev: PackedOption<Inst>,
    next: PackedOption<Inst>,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
struct BlockNode {
    prev: PackedOption<Block>,
    next: PackedOption<Block>,
    first: PackedOption<Inst>,
    last: PackedOption<Inst>,
}

/// Allows the blocks in a layout to be iterated over in program-order.
///
/// This isn't necessarily any relationship between this order and the
/// actual execution order of the SIR besides the fact that the first block
/// is the `entry` block.
#[derive(Copy, Clone, Debug)]
pub struct BlockIter<'layout> {
    next: Option<Block>,
    layout: &'layout Layout,
}

impl<'l> Iterator for BlockIter<'l> {
    type Item = Block;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|block| {
            self.next = self.layout.blocks[block].next.expand();

            block
        })
    }
}

/// Allows all of the instructions in a given block to be iterated over.
#[derive(Copy, Clone, Debug)]
pub struct InstIter<'layout> {
    next: Option<Inst>,
    layout: &'layout Layout,
}

impl<'l> Iterator for InstIter<'l> {
    type Item = Inst;

    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|inst| {
            self.next = self.layout.nodes[inst].next.expand();

            inst
        })
    }
}

/// Models the layout of an entire function and every basic-block in it.
///
/// Each block is modeled as a linked list to allow easy splicing and in-place
/// editing, and the list of blocks is also modeled as a linked list for
/// similar reasons.
#[derive(Default, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Layout {
    // forms a doubly-linked list of blocks, with `None` at the head/tail
    blocks: SecondaryMap<Block, BlockNode>,
    // forms a doubly-linked list of instructions, with `None` at the head/tail
    nodes: SecondaryMap<Inst, InstNode>,
    // maps instructions -> the blocks that contain them
    inst_blocks: SecondaryMap<Inst, Block>,
    // the first block in the layout, if any exist
    head: PackedOption<Block>,
    // the last block in the layout, if any exist
    tail: PackedOption<Block>,
    block_len: usize,
    inst_len: usize,
}

impl Layout {
    /// Creates a new, empty layout that is linked to the given data-flow graph.
    pub fn new() -> Self {
        Self::default()
    }

    /// Appends an instruction to the end of the specified block. If this is the final
    /// instruction being appended to the block, it must be a terminator instruction.
    pub fn append_inst(&mut self, inst: Inst, block: Block) {
        debug_assert!(
            !self.nodes.contains(inst),
            "cannot insert same inst multiple times"
        );

        let block_node = &mut self.blocks[block];
        let prev = block_node.last.replace(inst);

        // if the instruction we're inserting after doesn't exist we're the first instruction
        match prev {
            Some(prev) => self.nodes[prev].next = PackedOption::some(inst),
            None => {
                block_node.first.replace(inst);
            }
        }

        // insert `inst` as a real node in the linked list, point it at `prev` as the previous
        self.insert_node(inst, block, prev.into(), PackedOption::none());
    }

    /// Inserts `inst` into the same block as `before`, but directly before `before`.
    pub fn insert_inst_before(&mut self, inst: Inst, before: Inst) {
        debug_assert!(
            !self.nodes.contains(inst),
            "cannot insert same inst multiple times"
        );

        debug_assert!(
            self.nodes.contains(before),
            "cannot insert before instruction that doesn't exist in the layout"
        );

        let after = self.nodes[before].prev.replace(inst);

        // if the instruction we're inserting after doesn't exist, we're at the beginning
        // of the block's instruction list.
        match after {
            Some(after) => self.nodes[after].next = PackedOption::some(inst),
            None => {
                self.block_node_mut(before).first = PackedOption::some(inst);
            }
        }

        self.insert_node(
            inst,
            self.inst_blocks[before],
            after.into(),
            PackedOption::some(before),
        );
    }

    /// Inserts `inst` into the same block as `after`, but directly after `after`.
    pub fn insert_inst_after(&mut self, inst: Inst, after: Inst) {
        debug_assert!(
            !self.nodes.contains(inst),
            "cannot insert same inst multiple times"
        );

        debug_assert!(
            self.nodes.contains(after),
            "cannot insert after instruction that doesn't exist in the layout"
        );

        let before = self.nodes[after].next.replace(inst);

        // if the instruction we're inserting before doesn't exist, we're at the end
        // of the block's instruction list.
        match before {
            Some(before) => self.nodes[before].prev = PackedOption::some(inst),
            None => {
                self.block_node_mut(after).last = PackedOption::some(inst);
            }
        }

        self.insert_node(
            inst,
            self.inst_blocks[after],
            PackedOption::some(after),
            before.into(),
        );
    }

    /// Removes an instruction from the layout. It is expected that the instruction
    /// exists, because removing a non-existent instruction is almost certainly a bug.  
    pub fn remove_inst(&mut self, inst: Inst) {
        self.remove_inst_internal(inst, self.nodes[inst]);
    }

    /// In the case that removing an instruction that is possibly not in the layout
    /// is necessary, use this instead of [`Self::remove_inst`].
    ///
    /// Returns `true` an instruction was removed.
    pub fn remove_inst_if_exists(&mut self, inst: Inst) -> bool {
        match self.nodes.get(inst) {
            Some(node) => {
                self.remove_inst_internal(inst, *node);

                true
            }
            None => false,
        }
    }

    /// Appends a block to the layout, putting it at the end of the list of blocks.
    pub fn append_block(&mut self, block: Block) {
        debug_assert!(
            !self.blocks.contains(block),
            "cannot insert block that is already inserted"
        );

        let prev = self.tail.replace(block);

        // if tail exists, we need to mutate it as well. if it doesn't, we need
        // to make sure we also update the head since the list is empty
        match prev {
            Some(bb) => {
                self.blocks[bb].next.replace(block);
            }
            None => {
                self.head.replace(block);
            }
        }

        self.insert_block(block, prev, None);
    }

    /// Inserts a block before another block in the list.
    pub fn insert_block_before(&mut self, block: Block, before: Block) {
        debug_assert!(
            self.blocks.contains(before),
            "cannot insert before a block that doesn't exist in layout"
        );

        debug_assert!(
            !self.blocks.contains(block),
            "cannot insert block that is already inserted"
        );

        let after = self.blocks[before].prev.replace(block);

        match after {
            Some(after) => {
                self.blocks[after].next.replace(block);
            }
            None => {
                self.head.replace(block);
            }
        }

        self.insert_block(block, after, Some(before));
    }

    /// Inserts a basic block after another basic block.
    pub fn insert_block_after(&mut self, block: Block, after: Block) {
        debug_assert!(
            self.blocks.contains(after),
            "cannot insert after a block that doesn't exist in layout"
        );

        debug_assert!(
            !self.blocks.contains(block),
            "cannot insert block that is already inserted"
        );

        let before = self.blocks[after].next.replace(block);

        match before {
            Some(before) => {
                self.blocks[before].prev.replace(block);
            }
            None => {
                self.head.replace(block);
            }
        }

        self.insert_block(block, Some(after), before);
    }

    /// Returns the number of blocks in the layout
    pub fn len_blocks(&self) -> usize {
        self.block_len
    }

    /// Returns the number of instructions in the layout
    pub fn len_insts(&self) -> usize {
        self.inst_len
    }

    /// Checks if a block is currently inside the layout
    pub fn is_block_inserted(&self, block: Block) -> bool {
        self.blocks.contains(block)
    }

    /// Checks if an instruction is currently inside the layout
    pub fn is_inst_inserted(&self, inst: Inst) -> bool {
        self.nodes.contains(inst)
    }

    /// Gets an iterator over the blocks of the layout.
    pub fn blocks(&self) -> BlockIter<'_> {
        BlockIter {
            next: self.head.expand(),
            layout: self,
        }
    }

    /// Gets an iterator over every instruction in a given block.
    pub fn insts_in_block(&self, block: Block) -> InstIter<'_> {
        InstIter {
            next: self.blocks[block].first.expand(),
            layout: self,
        }
    }

    /// Gets the entry block for the layout, if it exists.
    pub fn entry_block(&self) -> Option<Block> {
        self.head.expand()
    }

    /// Gets the block that comes after `block`
    pub fn block_next(&self, block: Block) -> Option<Block> {
        self.blocks[block].next.expand()
    }

    /// Gets the block that comes before `block`
    pub fn block_prev(&self, block: Block) -> Option<Block> {
        self.blocks[block].prev.expand()
    }

    /// Gets the first instruction in `block`
    pub fn block_first_inst(&self, block: Block) -> Option<Inst> {
        self.blocks[block].first.expand()
    }

    /// Gets the last instruction in `block`
    pub fn block_last_inst(&self, block: Block) -> Option<Inst> {
        self.blocks[block].last.expand()
    }

    /// Gets the instruction that comes after `inst`
    pub fn inst_next(&self, inst: Inst) -> Option<Inst> {
        self.nodes[inst].next.expand()
    }

    /// Gets the instruction that comes before `inst`
    pub fn inst_prev(&self, inst: Inst) -> Option<Inst> {
        self.nodes[inst].prev.expand()
    }

    /// Gets the block that an instruction is in
    pub fn inst_block(&self, inst: Inst) -> Block {
        self.inst_blocks[inst]
    }

    fn insert_node(
        &mut self,
        inst: Inst,
        block: Block,
        prev: PackedOption<Inst>,
        next: PackedOption<Inst>,
    ) {
        self.nodes.insert(inst, InstNode { prev, next });
        self.inst_blocks.insert(inst, block);
        self.inst_len += 1;
    }

    // this is supposed to always be inlined to fold several bounds checks. borrow checker
    // doesn't really like it if I pass the nodes into the function along with &mut self,
    // but in order to see if the inst needs to be removed in one caller we index and see
    // if it exists. I don't want to just discard what we already loaded, so I force
    // this to be inlined to enable that to be folded
    fn remove_inst_internal(&mut self, inst: Inst, node: InstNode) {
        // update `node.prev` to point to `node.next` as its own next
        match node.prev.expand() {
            Some(prev) => {
                self.nodes[prev].next = node.next;
            }
            None => {
                self.block_node_mut(inst).first = node.next;
            }
        }

        // update `node.next` to point to `node.prev` as its own prev
        match node.next.expand() {
            Some(next) => {
                self.nodes[next].prev = node.prev;
            }
            None => {
                self.block_node_mut(inst).last = node.prev;
            }
        }

        // make sure there aren't ghost references to that instruction in the layout
        // anymore. we need to make it as-if the inst was never inserted to begin with
        self.nodes.remove(inst);
        self.inst_blocks.remove(inst);
        self.inst_len -= 1;
    }

    fn insert_block(&mut self, block: Block, prev: Option<Block>, next: Option<Block>) {
        self.block_len += 1;
        self.blocks.insert(
            block,
            BlockNode {
                prev: prev.into(),
                next: next.into(),
                first: PackedOption::none(),
                last: PackedOption::none(),
            },
        );
    }

    fn block_node_mut(&mut self, inst: Inst) -> &mut BlockNode {
        &mut self.blocks[self.inst_blocks[inst]]
    }
}

impl Debug for Layout {
    fn fmt(&self, _: &mut Formatter<'_>) -> fmt::Result {
        todo!()
    }
}
