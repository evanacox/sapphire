//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::arena::ArenaKey;
use crate::dense_arena_key;
use crate::ir::Value;
use crate::utility::Str;
use smallvec::{smallvec, SmallVec};

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

dense_arena_key! {
    /// References a single basic block in the program.
    ///
    /// Must be resolved with a [`DataFlowGraph`](crate::ir::DataFlowGraph) into an actual
    /// [`BasicBlock`] object.
    pub struct Block;
}

/// Models a single basic block in a function within the IR.
///
/// These are made up of two key things:
///
///   1. A linear sequence of instructions, ending in a terminator.
///   2. Zero or more basic-block parameters modeling the φs that the block has as input.
///
/// ```other
/// something(i32 %x):
///   %0 = iconst i32 42
///   %1 = imul i32 %x, %0
///   %2 = iconst i32 21862829
///   %3 = xor i32 %1, %2
///   br next(i32 %3)
/// ```
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct BasicBlock {
    data: SmallVec<[Value; 4]>,
}

impl BasicBlock {
    pub(in crate::ir) fn new(name: Str) -> Self {
        Self {
            data: smallvec![Value::key_new(name.0 as usize)],
        }
    }

    /// Gets the name of the block.
    pub fn name(&self) -> Str {
        Str(self.data[0].key_index() as u32)
    }

    /// Gets the parameters of the block.
    pub fn params(&self) -> &[Value] {
        &self.data[1..]
    }

    pub(in crate::ir) fn append_param(&mut self, val: Value) {
        self.data.push(val);
    }

    pub(in crate::ir) fn remove_param(&mut self, val: Value) {
        self.data
            .remove(self.data.iter().position(|v| *v == val).unwrap());
    }
}
