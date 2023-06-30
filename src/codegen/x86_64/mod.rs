//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! x86-64 Backend
//!
//! This is the main module for code specific to the generic "x86-64 backend,"
//! with code for general x86-64 codegen and code for specific ABIs on x86-64.

mod abi;
mod emit;
mod greedy_isel;
mod mir;
mod target;

pub use abi::*;
pub use emit::*;
pub use greedy_isel::*;
pub use mir::*;
pub use target::*;
