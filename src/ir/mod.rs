//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Provides the interfaces and the types required to properly
//! manipulate SIR.
//!
//! This only contains the code for representing and transforming the IR itself,
//! the transforms done by optimizations and whatnot are defined in other places.

mod block;
mod builders;
mod cursor;
mod data_flow;
mod debug;
mod function;
mod inst_builder;
mod instruction;
mod layout;
mod matcher;
mod module;
mod types;
mod value;
mod visitor;

pub use block::*;
pub use builders::*;
pub use cursor::*;
pub use data_flow::*;
pub use debug::*;
pub use function::*;
pub use inst_builder::*;
pub use instruction::*;
pub use layout::*;
pub use matcher::*;
pub use module::*;
pub use types::*;
pub use visitor::*;
