//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
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

mod backend;
mod common;
mod emitter;
mod isel;
mod legalize_aggregates;
mod mir;
pub mod patterns;
mod target;
pub mod x86_64;

pub use backend::*;
pub use common::*;
pub use emitter::*;
pub use isel::*;
pub use legalize_aggregates::*;
pub use mir::*;
pub use target::*;
