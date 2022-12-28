//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Provides several utility APIs that are used inside of various modules
//! inside of the compiler.
//!
//! This is the general catch-all for random utility code.

mod packed_option;
mod string_pool;
mod tiny;

pub use packed_option::*;
pub use string_pool::*;
pub use tiny::*;
