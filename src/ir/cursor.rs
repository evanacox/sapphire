//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::*;

/// Models the position that the cursor is "pointing at."
///
/// A cursor can be pointing at some block (either before the first instruction
/// in the block or after the last), at a specific instruction in a specific block,
/// or pointing at nothing.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum CursorPos {
    /// Pointing at nothing.
    Nothing,
    /// Pointing "before" the first instruction in a given block.
    ///
    /// ```none
    /// entry:
    ///   ; <-- here
    ///   %0 = iconst i32 42
    ///   %1 = iadd i32 %0, %0
    ///   ; ...
    /// ```
    Before(Block),
    /// Pointing at a specific instruction in a given block.
    ///
    /// ```none
    /// entry:
    ///   %0 = iconst i32 42 ; <-- here
    ///   %1 = iadd i32 %0, %0
    ///   ; ...
    /// ```
    At(Block, Inst),
    /// Pointing at the end of a specific block.
    ///
    /// ```none
    /// entry:
    ///   %0 = iconst i32 42
    ///   %1 = iadd i32 %0, %0
    ///   br one
    ///   ; <-- here
    /// ```
    After(Block),
}

#[inline(always)]
fn move_to_block_internal(this: &mut impl Cursor, next: Option<Block>) -> Option<Block> {
    this.set_pos(next.map_or_else(|| CursorPos::Nothing, CursorPos::Before));

    next
}

#[inline(always)]
fn move_to_inst_internal(this: &mut impl Cursor, next: Option<(Block, Inst)>) -> Option<Inst> {
    this.set_pos(next.map_or_else(
        || CursorPos::Nothing,
        |(block, inst)| CursorPos::At(block, inst),
    ));

    next.map(|(_, inst)| inst)
}

/// Models basic cursor operations that **view** a function. None of these operations
/// require mutable access to a given function, so they can be used inside of
/// analyses.
pub trait Cursor: Sized {
    /// Gets the current cursor position
    fn pos(&self) -> CursorPos;

    /// Sets the current cursor position
    fn set_pos(&mut self, pos: CursorPos);

    /// Returns the definition of the function being viewed
    fn def(&self) -> &FunctionDefinition;

    /// Gets the layout associated with the function being viewed
    fn layout(&self) -> &Layout {
        &self.def().layout
    }

    /// Gets the data-flow graph associated with the function being viewed
    fn dfg(&self) -> &DataFlowGraph {
        &self.def().dfg
    }

    /// Gets the current block being viewed by the cursor, if any.
    fn current_block(&self) -> Option<Block> {
        match self.pos() {
            CursorPos::Nothing => None,
            CursorPos::Before(block) | CursorPos::After(block) | CursorPos::At(block, _) => {
                Some(block)
            }
        }
    }

    /// Gets the current block being viewed by the cursor, if any.
    fn current_inst(&self) -> Option<Inst> {
        if let CursorPos::At(_, inst) = self.pos() {
            Some(inst)
        } else {
            None
        }
    }

    /// Tries to get the possible branch targets for the terminator of the current block.
    /// If there is no current block or the current block's last instruction is not a
    /// terminator, returns `None`.
    fn current_block_terminator_targets(&self) -> Option<&[BlockWithParams]> {
        let block = match self.current_block() {
            Some(bb) => bb,
            None => return None,
        };

        self.layout()
            .block_last_inst(block)
            .and_then(|inst| self.dfg().branch_info(inst))
    }

    /// Moves the position to `Before(block)`.
    fn goto_before(&mut self, block: Block) {
        debug_assert!(self.layout().is_block_inserted(block));

        self.set_pos(CursorPos::Before(block));
    }

    /// Moves the position to `After(block)`.
    fn goto_after(&mut self, block: Block) {
        debug_assert!(self.layout().is_block_inserted(block));

        self.set_pos(CursorPos::After(block));
    }

    /// Moves the position to `At(block, first_inst_in_block)`.
    fn goto_first_inst(&mut self, block: Block) {
        self.goto_before(block);

        self.next_inst();
    }

    /// Moves the position to `At(block, last_inst_in_block)`.
    fn goto_last_inst(&mut self, block: Block) {
        self.goto_after(block);

        self.prev_inst();
    }

    /// Moves the position to `At(containing, inst)`
    fn goto_inst(&mut self, inst: Inst) {
        debug_assert!(self.layout().is_inst_inserted(inst));

        let block = self.layout().inst_block(inst);

        self.set_pos(CursorPos::At(block, inst));
    }

    /// Moves the cursor to the next block in the function. If the cursor is currently
    /// not pointing to anywhere in the function, this moves it to `Before(entry)`. If the
    /// cursor is pointing at the last block in the function, this moves it to `Nothing`.
    fn next_block(&mut self) -> Option<Block> {
        let bb = self.current_block().map_or_else(
            || self.layout().entry_block(),
            |block| self.layout().block_next(block),
        );

        move_to_block_internal(self, bb)
    }

    /// Moves the cursor to the block before the current one. If the cursor is pointing at `Nothing`,
    /// nothing changes. If the cursor is pointing at the first block, its moved to `Nothing`.
    fn prev_block(&mut self) -> Option<Block> {
        let bb = self
            .current_block()
            .and_then(|block| self.layout().block_prev(block));

        move_to_block_internal(self, bb)
    }

    /// Moves the cursor to the next instruction in the function. If the cursor points
    /// before the block, this is the first instruction. If it points after, this does
    /// nothing. If it points at nothing, this does nothing.
    fn next_inst(&mut self) -> Option<Inst> {
        let block_and_inst = match self.pos() {
            CursorPos::Nothing | CursorPos::After(_) => None,
            CursorPos::At(block, inst) => self.layout().inst_next(inst).map(|inst| (block, inst)),
            CursorPos::Before(block) => self
                .def()
                .layout
                .block_first_inst(block)
                .map(|inst| (block, inst)),
        };

        move_to_inst_internal(self, block_and_inst)
    }

    /// Moves the cursor to the previous instruction in the function. If the cursor points
    /// after the block, this is the last instruction. If it points before, this does
    /// nothing. If it points at nothing, this does nothing.
    fn prev_inst(&mut self) -> Option<Inst> {
        let block_and_inst = match self.pos() {
            CursorPos::Nothing | CursorPos::Before(_) => None,
            CursorPos::At(block, inst) => self.layout().inst_prev(inst).map(|inst| (block, inst)),
            CursorPos::After(block) => self
                .def()
                .layout
                .block_last_inst(block)
                .map(|inst| (block, inst)),
        };

        move_to_inst_internal(self, block_and_inst)
    }
}

/// Effectively a [`FuncCursor`] without any of the operations
/// that mutate the function.
pub struct FuncView<'f> {
    func: &'f Function,
    pos: CursorPos,
}

impl<'f> Cursor for FuncView<'f> {
    fn pos(&self) -> CursorPos {
        self.pos
    }

    fn set_pos(&mut self, pos: CursorPos) {
        self.pos = pos;
    }

    fn def(&self) -> &FunctionDefinition {
        self.func
            .definition()
            .expect("cannot view function without a definition")
    }
}

impl<'f> FuncView<'f> {
    /// Creates a [`FuncView`] that allows the given function to be viewed.
    pub fn over(func: &'f Function) -> Self {
        Self {
            func,
            pos: CursorPos::Nothing,
        }
    }
}

/// Similar to [`FuncBuilder`] but for in-place modification of functions.
pub struct FuncCursor<'f> {
    func: &'f mut Function,
    pos: CursorPos,
}
