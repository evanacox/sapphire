//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! APIs for the compiler back-end and code-generation facilities
//!
//! These APIs mostly abstract away any target-specific details, but
//! there *is* target-specific code in this module. Anything in a module
//! with an architecture in its name (e.g. `sapphire::codegen::x86_64::*` or
//! `sapphire::codegen::aarch64::*`) are CPU-specific.

mod abi;
mod backend;
mod emitter;
mod isel;
mod mir;
mod options;
pub mod patterns;
mod regalloc;
mod rewriter;
mod ssa;
mod target;
pub mod x86_64;

pub use abi::*;
pub use backend::*;
pub use emitter::*;
pub use isel::*;
pub use mir::*;
pub use options::*;
pub use regalloc::*;
pub use rewriter::*;
pub use ssa::*;
pub use target::*;
