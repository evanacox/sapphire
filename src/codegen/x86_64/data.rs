//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::{FuncData, MIRBlock};

/// A single, self-contained constant for x86-64.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Constant {
    /// A `.quad` that refers to a label
    QuadLabel(MIRBlock),
    /// A `.quad` (8-byte) constant
    Quad(u64),
    /// A `.long` (4-byte) constant
    Long(u32),
    /// A `.short` (2-byte) constant
    Short(u16),
    /// A `.byte` (1-byte) constant
    Byte(u8),
    /// An array of constants with a specified relative order
    Array(Box<[Constant]>),
    /// A string constant that is **not** null-terminated by default
    String(Box<[char]>),
}

impl FuncData for Constant {}
