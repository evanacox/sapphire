//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! This module provides the interfaces and the types required to properly
//! manipulate the IR that Sapphire uses internally.
//!
//! This only contains the code for representing and transforming the IR itself,
//! the transforms done by optimizations and whatnot are defined in other places.

mod block;
mod data_flow;
mod debug;
mod function;
mod instruction;
mod module;
mod types;
mod value;

pub use block::*;
pub use data_flow::*;
pub use debug::*;
pub use function::*;
pub use instruction::*;
pub use module::*;
pub use types::*;
