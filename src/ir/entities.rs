//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::{BasicBlock, Block, InstData, Sig, Signature};
use slotmap::{new_key_type, SecondaryMap, SlotMap};
use static_assertions::assert_eq_size;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

new_key_type! {
    struct EntityRef;
}

/// A basic reference to some value, either the result of some computation
/// or an argument into a basic block. Since everything is based around
/// function-scoped values in SIR, this is effectively equivalent to a
/// `llvm::Value*`.
///
/// All values are owned and stored as [`ValueData`] objects,
/// but since those are large and expensive to move around these are
/// copied around instead.
///
/// These are completely useless without the associated [`EntityStorage`] they
/// come from, as they are just keys into a giant table. The DFG contains all the
/// information that actually makes these useful.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Value(EntityRef);

/// While [`Value`]s refer to a result of some sort, [`Inst`]s refer to
/// the instructions themselves. This has a subtly different meaning: an [`Inst`]
/// may not actually refer to something that produces a *result*.
///
/// Some instructions only perform side effects (e.g. `call void`, `store`), some
/// model control flow (e.g. `ret`, `br`), some simply do not produce a result
/// due to being more of a signal (e.g. `unreachable`). These can never be
/// referred to with [`Value`]s, but they *can* be referred to with [`Inst`]s.
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct Inst(EntityRef);

#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
enum EntityData {
    Instruction(InstData),
    Param(BlockParam),
}

#[repr(u32)]
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum ValueDef {
    Inst(Inst),
    Block(Block, u32),
}

assert_eq_size!(ValueDef, [u64; 2]);

/// Owns all of the instructions, basic blocks, values, and everything else
/// in a given function. Also models all the complex data-flow information between
/// various instructions, although it does not model .
///
///
#[derive(Debug, Clone)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct EntityStorage {
    blocks: SlotMap<Block, BasicBlock>,
    entities: SlotMap<EntityRef, EntityData>,
    values: SecondaryMap<EntityRef, ValueDef>,
    sigs: SlotMap<Sig, Signature>,
}

impl EntityStorage {
    /// Gets a function's [`Signature`] from a given [`Sig`]. Any [`Sig`]
    /// used by any indirect or direct calls inside the function body
    /// can be resolved here.
    pub fn signature(&self, sig: Sig) -> &Signature {
        &self.sigs[sig]
    }

    /// Gets a single instruction's [`InstructionData`] from a given [`Inst`].
    /// Any [`Inst`] used anywhere in this function can be resolved here.
    pub fn data(&self, inst: Inst) -> &InstData {
        match &self.entities[inst.0] {
            EntityData::Instruction(data) => data,
            _ => panic!("got an `Inst` that did not refer to an instruction"),
        }
    }

    pub fn create_inst(&)
}
