//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::dense_arena_key;
use crate::ir::{Inst, Value};
use smallvec::SmallVec;

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
#[derive(Debug, Clone, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct BasicBlock {
    body: SmallVec<[Inst; 2]>,
    params: SmallVec<[Value; 2]>,
}
