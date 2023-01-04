//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::{ArenaKey, ArenaMap, SecondaryMap, UniqueArenaMap};
use crate::dense_arena_key;
use crate::ir::{BasicBlock, Block, DebugInfo, InstData, Instruction, Sig, Signature, Type};
use crate::utility::Str;
use smallvec::SmallVec;
use static_assertions::assert_eq_size;
use std::collections::HashMap;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

dense_arena_key! {
    struct EntityRef;

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
        Self::new(key.index())
    }

    pub(in crate::ir) fn raw_into<T: ArenaKey>(self) -> T {
        T::new(self.index())
    }
}

// this enables us to turn `Inst`s into `Value`s or `EntityRef`s, this is very
// useful for compact storage in homogenous containers
impl Inst {
    pub(in crate::ir) fn raw_from(key: impl ArenaKey) -> Self {
        Self::new(key.index())
    }

    pub(in crate::ir) fn raw_into<T: ArenaKey>(self) -> T {
        T::new(self.index())
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
struct BlockParam {
    ty: Type,
    bb: Block,
    index: u32,
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
    blocks: ArenaMap<Block, BasicBlock>,
    block_names: HashMap<Str, Block, ahash::RandomState>,
    entities: ArenaMap<EntityRef, EntityData>,
    values: SecondaryMap<Value, ValueDefinition>,
    params: SecondaryMap<Block, SmallVec<[Value; 4]>>,
    debug: SecondaryMap<EntityRef, DebugInfo>,
    uses: SecondaryMap<Value, SmallVec<[Inst; 4]>>,
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
    pub fn data(&self, inst: Inst) -> &InstData {
        match &self.entities[inst.raw_into()] {
            EntityData::Inst(data) => data,
            _ => unreachable!("got an `Inst` that did not refer to an instruction"),
        }
    }

    /// Gets a single instruction's [`DebugInfo`](crate::ir::DebugInfo).
    pub fn inst_debug(&self, inst: Inst) -> DebugInfo {
        self.debug[inst.raw_into()]
    }

    /// Gets a single value's [`DebugInfo`](crate::ir::DebugInfo).
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
    pub fn insert_inst(&mut self, data: InstData, debug: DebugInfo) -> (Inst, Option<Value>) {
        let result = data.result_ty();
        let k = self.entities.insert(EntityData::Inst(data));
        let inst = Inst::raw_from(k);

        self.debug.insert(k, debug);

        match result {
            Some(result) => {
                let val = Value::raw_from(k);

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

    /// Inserts a basic block with a given name into the DFG. It will start with an empty
    /// list of block parameters, these can be appended later.
    pub fn insert_block(&mut self, name: Str) -> Block {
        let bb = self.blocks.insert(BasicBlock::new(name));

        self.block_names.insert(name, bb);

        bb
    }

    /// Finds a block by name, if it exists.
    pub fn find_block(&self, name: Str) -> Option<Block> {
        self.block_names.get(&name).copied()
    }

    /// Resolves a block into a full [`BasicBlock`].
    pub fn block(&self, block: Block) -> &BasicBlock {
        debug_assert!(self.is_block_inserted(block));

        &self.blocks[block]
    }

    /// Appends a block parameter to a given block.
    pub fn append_block_param(&mut self, bb: Block, ty: Type, debug: DebugInfo) -> Value {
        debug_assert!(self.is_block_inserted(bb));

        let block = &mut self.blocks[bb];
        let index = block.params().len() as u32;
        let param = BlockParam { bb, ty, index };
        let param = self.entities.insert(EntityData::Param(param));
        let val = Value::raw_from(param);

        block.append_param(val);

        self.debug.insert(param, debug);
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
}
