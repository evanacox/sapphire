//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::{ArenaKey, ArenaMap, SecondaryMap, SecondarySet, UniqueArenaMap};
use crate::dense_arena_key;
use crate::ir::{
    BasicBlock, Block, BlockWithParams, DebugInfo, InstData, Instruction, Sig, Signature,
    Terminator, Type,
};
use crate::utility::{SaHashMap, Str};
use smallvec::{smallvec, SmallVec};
use static_assertions::assert_eq_size;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

dense_arena_key! {
    struct EntityRef;

    /// A reference to a single slot on a function's pre-allocated stack.
    ///
    /// These are defined by the `$name = stack <ty>` directives before the first
    /// basic block in a function.
    pub struct StackSlot;

    /// A basic reference to some value, either the result of some computation
    /// or an argument into a basic block. Since everything is based around
    /// function-scoped values in SIR, this is effectively equivalent to a
    /// `llvm::Value*`.
    ///
    /// These are completely useless without the associated [`DataFlowGraph`] they
    /// come from, as they are just keys into a giant table. The DFG contains all the
    /// information that actually makes these useful.
    pub struct Value;

    /// While [`Value`]s refer to a result of some sort, [`Inst`]s refer to
    /// the instructions themselves. This has a subtly different meaning: an [`Inst`]
    /// may not actually refer to something that produces a *result*.
    ///
    /// Some instructions only perform side effects (e.g. `call void`, `store`), some
    /// model control flow (e.g. `ret`, `br`), some simply do not produce a result
    /// due to being more of a signal (e.g. `unreachable`). These can never be
    /// referred to with [`Value`]s, but they *can* be referred to with [`Inst`]s.
    pub struct Inst;
}

// this enables us to turn `Value`s into `Inst`s or `EntityRef`s, this is very
// useful for compact storage in homogenous containers
impl Value {
    pub(in crate::ir) fn raw_from(key: impl ArenaKey) -> Self {
        Self::key_new(key.key_index())
    }

    pub(in crate::ir) fn raw_into<T: ArenaKey>(self) -> T {
        T::key_new(self.key_index())
    }
}

// this enables us to turn `Inst`s into `Value`s or `EntityRef`s, this is very
// useful for compact storage in homogenous containers
impl Inst {
    pub(in crate::ir) fn raw_from(key: impl ArenaKey) -> Self {
        Self::key_new(key.key_index())
    }

    pub(in crate::ir) fn raw_into<T: ArenaKey>(self) -> T {
        T::key_new(self.key_index())
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
struct BlockParam {
    ty: Type,
    bb: Block,
    index: u32,
}

/// Contains information about a specific stack slot in a function.
///
/// This is just the name/type of it, since that's the only information
/// actually associated with one.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct StackSlotData {
    name: Str,
    ty: Type,
}

impl StackSlotData {
    /// Gets the name of the stack slot
    #[inline]
    pub fn name(self) -> Str {
        self.name
    }

    /// Gets the type that the stack slot is allocating space for
    #[inline]
    pub fn ty(self) -> Type {
        self.ty
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
enum EntityData {
    Inst(InstData),
    Param(BlockParam),
}

/// Models where a given value came from.
#[repr(u32)]
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum ValueDef {
    /// The value is the result yielded by an instruction
    Inst(Inst),
    /// The value is the nth block parameter of a block
    Param(Block, u32),
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
struct ValueDefinition {
    ty: Type,
    data: ValueDef,
}

assert_eq_size!(ValueDefinition, [u64; 2]);
assert_eq_size!(InstData, [u64; 4]);

/// Owns all of the instructions, basic blocks, values, and everything else
/// in a given function. Also models all the complex data-flow information between
/// various instructions, although it does not model any of the actual code layout
/// information (block ordering, instruction ordering, etc).
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct DataFlowGraph {
    //
    // fundamental magic for this whole data structure:
    //   1. every 'entity' (a block param or instruction) has a slot in `entities`
    //   2. every Inst has the same key value as its associated entity
    //   3. every Value has the same key value as the entity that *yields* it, and also has a slot in `values`
    //
    // this means that (valid) Insts and Values can **always** be used as EntityRefs, but Insts and
    // Values themselves can only be safely converted when its known that the inst referred to has a result
    sigs: UniqueArenaMap<Sig, Signature>,
    blocks: ArenaMap<Block, Option<BasicBlock>>,
    block_names: SaHashMap<Str, Block>,
    entities: ArenaMap<EntityRef, EntityData>,
    values: SecondaryMap<Value, ValueDefinition>,
    params: SecondaryMap<Block, SmallVec<[Value; 4]>>,
    debug: SecondaryMap<EntityRef, DebugInfo>,
    uses: SecondaryMap<Value, SmallVec<[Inst; 4]>>,
    stack_slots: ArenaMap<StackSlot, Option<StackSlotData>>,
    metadata_affecting_insts: SmallVec<[Inst; 4]>,
}

impl DataFlowGraph {
    /// Creates a new data-flow graph for a new function.
    pub fn new() -> Self {
        Self::default()
    }

    /// Gets a function's [`Signature`] from a given [`Sig`]. Any [`Sig`]
    /// used by any indirect or direct calls inside the function body
    /// can be resolved here.
    pub fn signature(&self, sig: Sig) -> &Signature {
        &self.sigs[sig]
    }

    /// Converts a [`Value`] into an [`Inst`] if and only if that value
    /// refers to an instruction's result. If `value` refers to a block
    /// parameter instead, `None` is returned.
    pub fn value_to_inst(&self, value: Value) -> Option<Inst> {
        match self.values[value].data {
            ValueDef::Inst(_) => Some(value.raw_into()),
            _ => None,
        }
    }

    /// Converts an [`Inst`] into a [`Value`] referring to its result if and only
    /// if that instruction actually yields a result. If it does not have a result,
    /// `None` is returned.
    pub fn inst_to_result(&self, inst: Inst) -> Option<Value> {
        self.values.get(inst.raw_into()).map(|_| inst.raw_into())
    }

    /// Gets a single instruction's [`InstData`].
    pub fn inst_data(&self, inst: Inst) -> &InstData {
        match &self.entities[inst.raw_into()] {
            EntityData::Inst(data) => data,
            _ => unreachable!("got an `Inst` that did not refer to an instruction"),
        }
    }

    /// Gets a single instruction's [`DebugInfo`].
    pub fn inst_debug(&self, inst: Inst) -> DebugInfo {
        self.debug[inst.raw_into()]
    }

    /// Gets a single value's [`DebugInfo`].
    pub fn debug(&self, inst: Value) -> DebugInfo {
        self.debug[inst.raw_into()]
    }

    /// Gets the type of the value that a given [`Value`] evaluates to.
    pub fn ty(&self, value: Value) -> Type {
        self.values[value].ty
    }

    /// Gets any values that are used as operands for computing `value`.
    ///
    /// This can potentially be empty, e.g. for block params or constant
    /// materialization instructions.
    pub fn operands(&self, value: Value) -> &[Value] {
        match &self.entities[value.raw_into()] {
            EntityData::Param(_) => &[],
            EntityData::Inst(i) => i.operands(),
        }
    }

    /// Inserts an instruction into the DFG, and returns a reference to it. If the instruction
    /// yields a result (and thus can also be used as an operand for other instructions), that
    /// value is also returned as the second return value.
    pub fn create_inst(&mut self, data: InstData, debug: DebugInfo) -> (Inst, Option<Value>) {
        let result = data.result_ty();
        let k = self.entities.next_key();

        for operand in data.operands() {
            self.uses[*operand].push(Inst::raw_from(k));
        }

        if let InstData::Alloca(_) | InstData::Call(_) | InstData::IndirectCall(_) = &data {
            self.metadata_affecting_insts.push(Inst::raw_from(k));
        }

        let _ = self.entities.insert(EntityData::Inst(data));
        self.uses.insert(Value::raw_from(k), smallvec![]);
        self.debug.insert(k, debug);

        self.maybe_result(k, result)
    }

    /// Inserts a basic block with a given name into the DFG. It will start with an empty
    /// list of block parameters, these can be appended later.
    pub fn create_block(&mut self, name: Str) -> Block {
        let bb = self.blocks.insert(Some(BasicBlock::new(name)));

        self.block_names.insert(name, bb);

        bb
    }

    /// Finds a block by name, if it exists.
    pub fn find_block(&self, name: Str) -> Option<Block> {
        self.block_names.get(&name).copied()
    }

    /// Iterates over every blocks
    pub fn all_blocks(&self) -> impl Iterator<Item = &BasicBlock> {
        self.blocks.values().flatten()
    }

    /// Resolves a block into a full [`BasicBlock`].
    pub fn block(&self, block: Block) -> &BasicBlock {
        debug_assert!(self.is_block_inserted(block));

        self.blocks[block].as_ref().unwrap()
    }

    /// Removes a basic block that already exists.
    pub fn remove_block(&mut self, block: Block) {
        debug_assert!(self.is_block_inserted(block));

        let _ = self.blocks.get_mut(block).unwrap().take();
    }

    /// Appends a block parameter to a given block.
    pub fn append_block_param(&mut self, bb: Block, ty: Type, debug: DebugInfo) -> Value {
        debug_assert!(self.is_block_inserted(bb));

        let block = self.blocks[bb].as_mut().unwrap();
        let index = block.params().len() as u32;
        let param = BlockParam { bb, ty, index };
        let param = self.entities.insert(EntityData::Param(param));
        let val = Value::raw_from(param);

        block.append_param(val);

        self.debug.insert(param, debug);
        self.uses.insert(val, smallvec![]);
        self.values.insert(
            val,
            ValueDefinition {
                ty,
                data: ValueDef::Param(bb, index),
            },
        );

        val
    }

    /// Inserts a function signature into the signature arena (if it
    /// isn't already in the arena), and returns a [`Sig`] that can
    /// refer to it.
    pub fn insert_sig(&mut self, sig: &Signature) -> Sig {
        self.sigs.insert_clone_if(sig)
    }

    /// Checks if the DFG contains a given instruction. If it does not, the
    /// instruction is invalid. Any instruction returned from one of the `insert_inst_*` methods
    /// will be contained.
    pub fn is_inst_inserted(&self, inst: Inst) -> bool {
        self.entities.contains(inst.raw_into())
    }

    /// Checks if the DFG contains a given value. If it does not, the
    /// value is invalid. Any values returned from one of the `insert_inst_*`
    /// methods or the [`Self::append_block_param`] method will be contained.
    pub fn is_val_inserted(&self, value: Value) -> bool {
        self.entities.contains(value.raw_into())
    }

    /// Checks if the DFG contains a given block. If the block was returned from
    /// any of the block insertion methods, it will be contained.
    pub fn is_block_inserted(&self, block: Block) -> bool {
        self.blocks.contains(block)
    }

    /// Gets the definition of a given value
    pub fn value_def(&self, val: Value) -> ValueDef {
        self.values[val].data
    }

    /// Checks if a given value is a block parameter.
    pub fn is_block_param(&self, val: Value) -> bool {
        matches!(self.values[val].data, ValueDef::Param(_, _))
    }

    /// If an instruction is a terminator, returns the list of branch targets. If it
    /// isn't, returns `None`.
    pub fn branch_info(&self, inst: Inst) -> Option<&'_ [BlockWithParams]> {
        match &self.entities[inst.raw_into()] {
            EntityData::Inst(data) => match data {
                InstData::Br(br) => Some(br.targets()),
                InstData::CondBr(condbr) => Some(condbr.targets()),
                InstData::Ret(_) | InstData::Unreachable(_) => Some(&[]),
                _ => None,
            },
            _ => None,
        }
    }

    /// Replaces `inst` with new data and new debuginfo. This makes all references
    /// to that [`Inst`] point to this new instruction instead.
    pub fn replace_inst(
        &mut self,
        inst: Inst,
        data: InstData,
        debug: DebugInfo,
    ) -> (Inst, Option<Value>) {
        debug_assert!(self.is_inst_inserted(inst));

        let result = data.result_ty();
        let k = inst.raw_into();
        let slot = match &mut self.entities[inst.raw_into()] {
            EntityData::Inst(data) => data,
            _ => unreachable!(),
        };

        for operand in slot.operands() {
            if !data.operands().contains(operand) {
                let v = &mut self.uses[*operand];
                let idx = v.iter().position(|&i| i == inst).unwrap();

                v.swap_remove(idx);
            }
        }

        for operand in data.operands() {
            self.uses[*operand].push(Inst::raw_from(k));
        }

        *slot = data;
        self.debug.insert(k, debug);

        self.maybe_result(k, result)
    }

    /// Returns every use in the data-flow graph of a given value.
    ///
    /// Note that all of these may not actually exist in the function layout.
    /// If you don't want to pointlessly iterate over these, filter this
    /// by the ones that are present in a given layout.
    pub fn uses_of(&self, val: Value) -> &[Inst] {
        &self.uses[val]
    }

    /// Replaces every use of `original` with `new`.
    pub fn replace_uses_with(&mut self, original: Value, new: Value) {
        let original_uses = std::mem::take(&mut self.uses[original]);

        self.uses[new].extend_from_slice(&original_uses);

        for inst in original_uses {
            let data = match &mut self.entities[inst.raw_into()] {
                EntityData::Inst(data) => data,
                _ => unreachable!("got an `Inst` that did not refer to an instruction"),
            };

            if let InstData::CondBr(inst) = data {
                inst.replace_use(original, new);
            } else {
                for v in data.__operands_dfg_mut() {
                    if *v == original {
                        *v = new;
                    }
                }
            }
        }
    }

    /// Gets one past the highest possible value key. This is an invalid key,
    /// but it is suitable for use with [`SecondaryMap::fill`].
    pub fn next_value(&self) -> Value {
        Value::raw_from(self.entities.next_key())
    }

    /// Removes a block parameter from a given block without invalidating references
    /// to the other block parameters. Note that this does change the index
    /// for other block parameters, but it doesn't make their [`Value`]s invalid.
    pub fn remove_block_param(&mut self, block: Block, param: Value) {
        debug_assert_eq!(self.uses_of(param), []);

        let block = self.blocks[block].as_mut().unwrap();

        block.remove_param(param);

        // need to update the indices of each parameter
        for (i, &val) in block.params().iter().enumerate() {
            match &mut self.entities[val.raw_into()] {
                EntityData::Param(param) => {
                    param.index = i as u32;
                }
                _ => unreachable!(),
            }

            match &mut self.values[val].data {
                ValueDef::Param(_, index) => *index = i as u32,
                _ => unreachable!(),
            }
        }
    }

    /// Rewrites a branch instruction that targets `target` to have a new set of block params
    pub fn rewrite_branch_args(&mut self, branch: Inst, target: Block, new_params: &[Value]) {
        let data = match &mut self.entities[branch.raw_into()] {
            EntityData::Inst(data) => data,
            _ => unreachable!("got an `Inst` that did not refer to an instruction"),
        };

        let targets = match data {
            InstData::Br(br) => br.targets(),
            InstData::CondBr(condbr) => condbr.targets(),
            InstData::Ret(_) | InstData::Unreachable(_) => &mut [],
            _ => unreachable!("got an `Inst` that did not refer to a terminator"),
        };

        let idx = targets
            .iter()
            .position(|t| t.block() == target)
            .expect("cannot rewrite branch that doesn't target `target`");

        let branch_target = &targets[idx];

        // need to make sure uses aren't made stale. we go through and remove
        // branch as a user for args that aren't present anymore, and we
        // add branch as a user for args that are present
        for val in branch_target.args() {
            if !new_params.contains(val) {
                let v = &mut self.uses[*val];

                v.swap_remove(
                    v.iter()
                        .position(|&inst| inst == branch)
                        .expect("uses are stale"),
                );
            }
        }

        for val in new_params {
            if !self.uses[*val].contains(&branch) {
                self.uses[*val].push(branch);
            }
        }

        match data {
            InstData::Br(br) => br.rewrite_branch_args(new_params),
            InstData::CondBr(condbr) => condbr.rewrite_branch_args(idx, new_params),
            _ => {}
        }
    }

    /// Replaces a single argument to a branch target on a branch instruction. This is intended
    /// to be more efficient for the more common case where a value is only being *replaced*
    /// instead of inserted/removed.
    pub fn replace_branch_arg(&mut self, inst: Inst, to: Block, arg: usize, new: Value) {
        let data = match &mut self.entities[inst.raw_into()] {
            EntityData::Inst(data) => data,
            _ => unreachable!("got an `Inst` that did not refer to an instruction"),
        };

        // get the old value occupying that slot of the arguments
        let old = match data {
            InstData::Br(br) => {
                debug_assert_eq!(br.target().block(), to);

                let old = br.target().args()[arg];

                br.replace_branch_arg(arg, new);

                old
            }
            InstData::CondBr(condbr) => {
                let idx = (condbr.false_branch().block() == to) as usize;

                let old = {
                    let target = if condbr.true_branch().block() == to {
                        condbr.true_branch()
                    } else {
                        condbr.false_branch()
                    };

                    target.args()[arg]
                };

                condbr.replace_branch_arg(idx, arg, new);

                old
            }
            _ => return,
        };

        // update uses information
        let inst_idx = self.uses[old].iter().position(|i| *i == inst).unwrap();
        self.uses[old].swap_remove(inst_idx);

        if !self.uses[new].contains(&inst) {
            self.uses[new].push(inst);
        }
    }

    /// Rewrites a branch that targets `to` to instead branch to `new` (with the args associated
    /// with `new`).
    ///
    /// Returns the old branch target so you can re-use the arguments.
    pub fn rewrite_branch_target(
        &mut self,
        inst: Inst,
        to: Block,
        new: BlockWithParams,
    ) -> BlockWithParams {
        let data = match &mut self.entities[inst.raw_into()] {
            EntityData::Inst(data) => data,
            _ => unreachable!("got an `Inst` that did not refer to an instruction"),
        };

        // get the old value occupying that slot of the arguments
        match data {
            InstData::Br(br) => {
                debug_assert_eq!(br.target().block(), to);

                br.replace_target(new)
            }
            InstData::CondBr(condbr) => {
                let idx = (condbr.false_branch().block() == to) as usize;

                condbr.replace_target(idx, new)
            }
            _ => unreachable!(),
        }
    }

    /// Creates a new stack slot with a given name and type.
    pub fn create_stack_slot(&mut self, name: Str, ty: Type) -> StackSlot {
        debug_assert!(
            !self
                .stack_slots
                .values()
                .any(|data| data.is_some() && data.unwrap().name == name),
            "no stack slots should have the same name"
        );

        self.stack_slots.insert(Some(StackSlotData { name, ty }))
    }

    /// Gets the information about a particular stack slot
    pub fn stack_slot(&self, slot: StackSlot) -> StackSlotData {
        self.stack_slots
            .get(slot)
            .copied()
            .flatten()
            .expect("tried to access invalid stack slot")
    }

    /// Provides an iterator over every stack slot in the function
    pub fn stack_slots(&self) -> impl Iterator<Item = StackSlot> + '_ {
        self.stack_slots
            .keys()
            .filter(|key| self.stack_slots[*key].is_some())
    }

    /// Checks if a given slot is actually a valid stack slot
    pub fn is_stack_slot_inserted(&self, slot: StackSlot) -> bool {
        self.stack_slots.contains(slot)
    }

    /// Removes a stack slot that already exists.
    pub fn remove_stack_slot(&mut self, slot: StackSlot) {
        debug_assert!(self.is_stack_slot_inserted(slot));

        let _ = self.stack_slots.get_mut(slot).unwrap().take();
    }

    /// Returns a [`SecondarySet`](arena::SecondarySet) that contains every
    /// value with exactly one use in the DFG.
    ///
    /// **Note: This may include values that are NOT in the associated function layout!**
    pub fn all_single_use_values(&self) -> SecondarySet<Value> {
        let mut map = SecondarySet::with_capacity(self.values.capacity());

        for value in self.values.keys() {
            if self.uses_of(value).len() == 1 {
                map.insert(value);
            }
        }

        map
    }

    /// Gets the instructions that can affect the function's metadata in some way
    pub(in crate::ir) fn all_metadata_affecting_insts(&self) -> &[Inst] {
        &self.metadata_affecting_insts
    }

    fn maybe_result(&mut self, key: EntityRef, result: Option<Type>) -> (Inst, Option<Value>) {
        let inst = Inst::raw_from(key);

        match result {
            Some(result) => {
                let val = Value::raw_from(key);

                self.values.insert(
                    val,
                    ValueDefinition {
                        ty: result,
                        data: ValueDef::Inst(inst),
                    },
                );

                (inst, Some(val))
            }
            None => (inst, None),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::analysis::stringify_module;
    use crate::ir::*;

    #[test]
    fn test_dfg_use_tracking_append() {
        let mut module = Module::new("test");
        let mut b =
            module.define_function("test", SigBuilder::new().ret(Some(Type::i32())).build());

        let bb0 = b.create_block("bb0");
        let bb1 = b.create_block("bb1");
        let v1 = b.append_block_param(bb1, Type::i32(), DebugInfo::fake());
        b.switch_to(bb0);

        let v0 = b.append().iconst(Type::i32(), 42, DebugInfo::fake());

        assert_eq!(b.dfg().uses_of(v0), []);
        assert_eq!(b.dfg().uses_of(v1), []);

        let br = b
            .append()
            .br(BlockWithParams::new(bb1, &[v0]), DebugInfo::fake());

        assert_eq!(b.dfg().uses_of(v0), [br]);
        assert_eq!(b.dfg().uses_of(v1), []);

        b.switch_to(bb1);
        let ret = b.append().ret_val(v1, DebugInfo::fake());

        assert_eq!(b.dfg().uses_of(v0), [br]);
        assert_eq!(b.dfg().uses_of(v1), [ret]);
    }

    #[test]
    fn test_dfg_use_tracking_replace() {
        let mut module = Module::new("test");
        let mut b =
            module.define_function("test", SigBuilder::new().ret(Some(Type::i32())).build());

        let bb0 = b.create_block("bb0");
        let bb1 = b.create_block("bb1");
        let v1 = b.append_block_param(bb1, Type::i32(), DebugInfo::fake());
        b.switch_to(bb0);

        let v0 = b.append().iconst(Type::i32(), 42, DebugInfo::fake());
        let br = b
            .append()
            .br(BlockWithParams::new(bb1, &[v0]), DebugInfo::fake());

        b.switch_to(bb1);
        let ret = b.append().ret_val(v1, DebugInfo::fake());

        assert_eq!(b.dfg().uses_of(v0), [br]);
        assert_eq!(b.dfg().uses_of(v1), [ret]);

        let f = b.define();
        let func = module.function_mut(f);
        let mut cursor = FuncCursor::over(func);

        cursor.goto_inst(ret);
        let v2 = cursor.insert().iconst(Type::i32(), 16, DebugInfo::fake());

        assert_eq!(cursor.dfg().uses_of(v2), []);

        let ret2 = cursor.replace().ret_val(v2, DebugInfo::fake());

        assert_eq!(cursor.dfg().uses_of(v2), [ret2]);
        assert_eq!(cursor.dfg().uses_of(v1), []);

        assert_eq!(
            stringify_module(&module),
            r#"fn i32 @test() {
bb0:
  %0 = iconst i32 42
  br bb1(i32 %0)

bb1(i32 %1):
  %2 = iconst i32 16
  ret i32 %2
}
"#
        )
    }
}
