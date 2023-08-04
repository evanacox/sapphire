//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! A hand-written parser and lexer meant to replace the Pest-based generated
//! parser.
//!
//! It should be significantly faster in every case than the Pest version.

mod lex;
mod parse;

pub use lex::*;
pub use parse::*;
