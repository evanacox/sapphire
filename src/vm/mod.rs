//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Provides APIs for the execution of SIR.
//!
//! This module defines the abstract interface of an "engine" that executes
//! some given SIR, and implementations of that abstract interface.
//!
//! An interpreter and a JIT will eventually be implemented with this
//! interface.

mod engine;
mod runtime;

pub use engine::*;
pub use runtime::*;
