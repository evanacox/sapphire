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
use crate::utility::Str;

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

    /// Tries to get the terminator of the current block. If there is no current block
    /// or the current block's last instruction is not a terminator, returns `None`.
    fn current_block_terminator(&self) -> Option<Inst> {
        let block = match self.current_block() {
            Some(bb) => bb,
            None => return None,
        };

        self.layout().block_last_inst(block)
    }

    /// Gets the debuginfo associated with the current instruction
    fn current_inst_dbg(&self) -> Option<DebugInfo> {
        self.current_inst().map(|inst| self.dfg().inst_debug(inst))
    }

    /// Moves the position to `Nothing`.
    fn goto_function_begin(&mut self) {
        self.set_pos(CursorPos::Nothing);
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
        let (maybe_inst, inst) = match self.pos() {
            CursorPos::Nothing | CursorPos::After(_) => (self.pos(), None),
            CursorPos::At(block, inst) => match self.layout().inst_next(inst) {
                Some(next) => (CursorPos::At(block, next), Some(next)),
                None => (CursorPos::After(block), None),
            },
            CursorPos::Before(block) => match self.layout().block_first_inst(block) {
                Some(first) => (CursorPos::At(block, first), Some(first)),
                None => (CursorPos::After(block), None),
            },
        };

        self.set_pos(maybe_inst);

        inst
    }

    /// Moves the cursor to the previous instruction in the function. If the cursor points
    /// after the block, this is the last instruction. If it points before, this does
    /// nothing. If it points at nothing, this does nothing.
    fn prev_inst(&mut self) -> Option<Inst> {
        let (maybe_inst, inst) = match self.pos() {
            CursorPos::Nothing | CursorPos::Before(_) => (self.pos(), None),
            CursorPos::At(block, inst) => match self.layout().inst_prev(inst) {
                Some(next) => (CursorPos::At(block, next), Some(next)),
                None => (CursorPos::Before(block), None),
            },
            CursorPos::After(block) => match self.layout().block_last_inst(block) {
                Some(first) => (CursorPos::At(block, first), Some(first)),
                None => (CursorPos::Before(block), None),
            },
        };

        self.set_pos(maybe_inst);

        inst
    }

    /// Converts an [`Inst`] into a [`Value`] that refers to the result
    /// of the instruction if possible.
    ///
    /// Not all instructions actually yield results, those will return `None`
    fn inst_to_result(&self, inst: Inst) -> Option<Value> {
        self.def().dfg.inst_to_result(inst)
    }

    /// Converts a [`Value`] into an [`Inst`] that yields that value, if possible.
    ///
    /// A block param has no associated inst, that will return `None`.
    fn value_to_inst(&self, val: Value) -> Option<Inst> {
        self.def().dfg.value_to_inst(val)
    }

    /// Checks if a given block is the entry block to the function
    fn is_entry_block(&self, block: Block) -> bool {
        self.def().layout.entry_block() == Some(block)
    }

    /// Gets the entry block of the function. Unless no blocks have been
    /// appended to the function, this will be `Some`.
    fn entry_block(&self) -> Option<Block> {
        self.def().layout.entry_block()
    }

    /// Gets the type of a value that was previously emitted by the builder.
    fn ty(&self, value: Value) -> Type {
        self.def().dfg.ty(value)
    }

    /// Gets the name of a block that has been inserted into the function
    fn block_name(&self, block: Block) -> Str {
        debug_assert!(self.def().layout.is_block_inserted(block));

        self.def().dfg.block(block).name()
    }

    /// Gets the block parameters of a given block.
    fn block_params(&self, block: Block) -> &[Value] {
        debug_assert!(self.def().layout.is_block_inserted(block));

        self.def().dfg.block(block).params()
    }

    /// Gets the definition of a given value
    fn value_def(&self, value: Value) -> ValueDef {
        self.def().dfg.value_def(value)
    }

    /// Gets the data defining a given instruction
    fn inst_data(&self, inst: Inst) -> &InstData {
        self.def().dfg.inst_data(inst)
    }

    /// Gets the block that an instruction is defined in
    fn inst_block(&self, inst: Inst) -> Block {
        self.layout().inst_block(inst)
    }

    /// If the instruction given is a branch instruction, returns the potential
    /// branch targets.
    ///
    /// Note that this does not care about if they are actually *reachable* targets,
    /// this cares about if the instruction mentions them or not. `condbr false a, b` would
    /// return `a` and `b` here.
    fn branch_info(&self, inst: Inst) -> Option<&[BlockWithParams]> {
        self.dfg().branch_info(inst)
    }

    /// Returns the debug information for a given instruction
    fn inst_debug(&self, inst: Inst) -> DebugInfo {
        self.dfg().inst_debug(inst)
    }

    /// Returns the debug information for a given instruction
    fn val_debug(&self, val: Value) -> DebugInfo {
        self.dfg().debug(val)
    }

    /// Returns the information about a given stack slot
    fn stack_slot(&self, slot: StackSlot) -> StackSlotData {
        self.dfg().stack_slot(slot)
    }
}

/// A builder that replaces an instruction with a new one
pub struct ReplaceBuilder<'b> {
    def: &'b mut FunctionDefinition,
    pos: Inst,
}

impl<'b> InstBuilder<'b> for ReplaceBuilder<'b> {
    fn dfg(&self) -> &DataFlowGraph {
        &self.def.dfg
    }

    fn build(self, data: InstData, debug: DebugInfo) -> (Inst, Option<Value>) {
        debug_assert_eq!(
            self.def.dfg.inst_data(self.pos).result_ty(),
            data.result_ty(),
            "cannot replace inst with inst of different result"
        );

        self.def.dfg.replace_inst(self.pos, data, debug)
    }
}

/// A builder that inserts an instruction between/before other ones.
pub struct InsertBuilder<'b> {
    def: &'b mut FunctionDefinition,
    pos: CursorPos,
}

impl<'b> InstBuilder<'b> for InsertBuilder<'b> {
    fn dfg(&self) -> &DataFlowGraph {
        &self.def.dfg
    }

    fn build(self, data: InstData, debug: DebugInfo) -> (Inst, Option<Value>) {
        let (inst, val) = self.def.dfg.create_inst(data, debug);

        match self.pos {
            CursorPos::At(_, before) => self.def.layout.insert_inst_before(inst, before),
            CursorPos::After(bb) => self.def.layout.append_inst(inst, bb),
            _ => panic!("move to either At(inst) or After(block) before inserting"),
        }

        (inst, val)
    }
}

/// A cursor with additional methods for mutating the IR.
pub trait CursorMut: Cursor {
    /// Gets a mutable reference to the function's definition.
    fn def_mut(&mut self) -> &mut FunctionDefinition;

    /// Gets a mutable reference to the function itself
    fn func_mut(&mut self) -> &mut Function;

    /// Returns an instruction builder that replaces the current instruction.
    fn replace(&mut self) -> ReplaceBuilder<'_> {
        let pos = self.pos();

        ReplaceBuilder {
            def: self.def_mut(),
            pos: match pos {
                CursorPos::At(_, inst) => inst,
                _ => panic!("move cursor to At(inst) before replacing"),
            },
        }
    }

    /// Allows an instruction to be inserted before the current one being pointed at.
    ///
    /// If this points at `At(inst)`, an instruction is inserted before `inst`. If
    /// this is pointing at `After(bb)`, an instruction is appended. Either way, the cursor
    /// is not moved, so repeated [`Self::insert`] calls make the instructions appear
    /// in the same order in the program.
    fn insert(&mut self) -> InsertBuilder<'_> {
        let pos = self.pos();

        InsertBuilder {
            def: self.def_mut(),
            pos,
        }
    }

    /// Replaces any uses of `original` in the function with `new`.
    fn replace_uses_with(&mut self, original: Value, new: Value) {
        self.def_mut().dfg.replace_uses_with(original, new)
    }

    /// Removes the current instruction and leaves the cursor pointing at the instruction
    /// immediately following the one that was removed.
    ///
    /// Returns the instruction that was removed.
    fn remove_inst(&mut self) -> Inst {
        let inst = self
            .current_inst()
            .expect("must be pointing at inst to remove");

        self.next_inst();
        self.def_mut().layout.remove_inst(inst);

        inst
    }

    /// Removes the current instruction and leaves the cursor pointing at the instruction
    /// immediately before the one that was removed.
    ///
    /// Returns the instruction that was removed.
    fn remove_inst_and_move_back(&mut self) -> Inst {
        let inst = self
            .current_inst()
            .expect("must be pointing at inst to remove");

        self.prev_inst();
        self.def_mut().layout.remove_inst(inst);

        inst
    }

    /// Removes a block parameter from a given block.
    fn remove_block_param(&mut self, block: Block, param: Value) {
        debug_assert!(self.layout().is_block_inserted(block));
        debug_assert!(matches!(self.value_def(param), ValueDef::Param(bb, _) if bb == block));

        self.def_mut().dfg.remove_block_param(block, param);
    }

    /// Rewrites the arguments of a given branch to match `new`
    fn rewrite_branch_args(&mut self, branch: Inst, target: Block, new: &[Value]) {
        self.def_mut().dfg.rewrite_branch_args(branch, target, new)
    }

    /// Rewrites a branch to `target` to have `new` as the `index`th argument
    fn replace_branch_arg(&mut self, branch: Inst, target: Block, index: usize, new: Value) {
        self.def_mut()
            .dfg
            .replace_branch_arg(branch, target, index, new)
    }

    /// Removes the current block, and moves to the next one.
    fn remove_block(&mut self) {
        let curr = self
            .current_block()
            .expect("cannot remove block when pointing at CursorPos::Nothing");

        let _ = self.next_block();

        self.def_mut().dfg.remove_block(curr);
    }

    /// Removes a single stack slot.
    fn remove_stack_slot(&mut self, slot: StackSlot) {
        self.def_mut().dfg.remove_stack_slot(slot);
    }

    /// Creates a single basic block and returns it. This block is appended to
    /// the end of the block list.
    ///
    /// Note that this does not switch the cursor to operate on that block,
    /// you still need to call `goto_before` or similar.
    fn create_block(&mut self, name: &str) -> Block {
        let string = {
            let mut strings = self.func_mut().ctx().strings_mut();

            strings.insert(name)
        };

        let block = self.def_mut().dfg.create_block(string);

        self.def_mut().layout.append_block(block);

        block
    }

    /// Equivalent to [`Self::create_block`], except it inserts the block before `before`
    /// instead of appending it.
    fn create_block_before(&mut self, name: &str, before: Block) -> Block {
        let string = {
            let mut strings = self.func_mut().ctx().strings_mut();

            strings.insert(name)
        };

        let block = self.def_mut().dfg.create_block(string);

        self.def_mut().layout.insert_block_before(block, before);

        block
    }

    /// Equivalent to [`Self::create_block`], except it inserts the block after `after`
    /// instead of appending it.
    fn create_block_after(&mut self, name: &str, after: Block) -> Block {
        let string = {
            let mut strings = self.func_mut().ctx().strings_mut();

            strings.insert(name)
        };

        let block = self.def_mut().dfg.create_block(string);

        self.def_mut().layout.insert_block_after(block, after);

        block
    }

    /// Rewrites the branch at the end of the current block that targets `to` to
    /// instead branch to `new` (with the args associated with `new`).
    ///
    /// Returns the old branch target so you can re-use the arguments.
    fn rewrite_branch_target(&mut self, to: Block, new: BlockWithParams) -> BlockWithParams {
        let inst = self
            .current_block_terminator()
            .expect("should have terminator");

        self.def_mut().dfg.rewrite_branch_target(inst, to, new)
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
    /// The function being moved over, public so it can be re-borrowed.
    pub func: &'f mut Function,
    pos: CursorPos,
}

impl<'f> FuncCursor<'f> {
    /// Creates a [`FuncCursor`] that allows the given function to be modified.
    pub fn over(func: &'f mut Function) -> Self {
        Self {
            func,
            pos: CursorPos::Nothing,
        }
    }
}

impl<'f> Cursor for FuncCursor<'f> {
    fn pos(&self) -> CursorPos {
        self.pos
    }

    fn set_pos(&mut self, pos: CursorPos) {
        self.pos = pos;
    }

    fn def(&self) -> &FunctionDefinition {
        self.func.definition().unwrap()
    }
}

impl<'f> CursorMut for FuncCursor<'f> {
    fn def_mut(&mut self) -> &mut FunctionDefinition {
        self.func.definition_mut().unwrap()
    }

    fn func_mut(&mut self) -> &mut Function {
        self.func
    }
}
