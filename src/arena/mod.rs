//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! A simple typed arena module.
//!
//! These arenas mostly do not allow deletion (besides [`SecondaryMap`]) and
//! provide configurable index sizes for extra flexibility and performance.
//! It is used extensively for forming graphs and other complex data structures
//! needed inside the compiler for representing different IRs.
//!
//! Very similar to `id_arena` and other simple typed arena crates, except this
//! one ties in better with the specific needs of this compiler (and does
//! less safety checks in exchange for significantly reduced overhead per slot).
//!
//! ```
//! # use sapphire::arena_key;
//! # use sapphire::arena::*;
//! arena_key! {
//!     pub struct Node;
//! }
//!
//! enum AstNode {
//!     Immediate(u64),
//!     Add(Node, Node),
//!     Mul(Node, Node)
//! }
//!
//! let mut arena = ArenaMap::new();
//!
//! // (16 + 3) * 3
//! let e1: Node = arena.insert(AstNode::Immediate(16)); // => 16
//! let e2 = arena.insert(AstNode::Immediate(3)); // => 3
//! let e3 = arena.insert(AstNode::Add(e1, e2)); // => (16 + 3)
//! let e4 = arena.insert(AstNode::Mul(e2, e3)); // => (16 + 3) * 3
//! ```

pub(in crate::arena) fn debug_write_map<'a, K, V>(
    f: &mut Formatter<'_>,
    name: &'static str,
    it: impl Iterator<Item = (K, &'a V)>,
) -> fmt::Result
where
    K: ArenaKey,
    V: Debug + 'a,
{
    write!(f, "{name} ")?;

    f.debug_map().entries(it).finish()
}

mod iter;
mod key;
mod map;
mod secondary;
mod unique;

pub use key::ArenaKey;
pub use map::ArenaMap;
pub use secondary::SecondaryMap;
use std::fmt;
use std::fmt::{Debug, Formatter};
pub use unique::UniqueArenaMap;
