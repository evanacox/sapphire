//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::utility::{PackedOption, Str};
use static_assertions::assert_eq_size;

#[cfg(feature = "enable-serde")]
use serde::{Deserialize, Serialize};

/// Holds the "debug info" for an instruction, i.e. where it came from.
///
/// This is necessary information for testing analysis passes and providing
/// meaningful error information, so this is required for every instruction. It also
/// makes it possible to potentially generate debug information from SIR at some point.
///
/// The expectation of where this info came from depends on where the instruction
/// came from:
///
///   1. The instruction was compiled from some line of source code, in which case
///      multiple SIR instructions may have the same debug information.
///
///   2. The instruction came from a file containing textual SIR, in which case
///      each instruction will have unique debug information.
///
#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct DebugInfo {
    name: PackedOption<Str>,
    col: u32,
    line: u32,
    file: Str,
}

impl DebugInfo {
    /// Creates a new [`DebugInfo`] object that has all the fields
    /// filled in (except the name).
    ///
    /// This is intended to be for creating SIR from a higher-level
    /// language where `col` is actually meaningful.
    pub fn new(line: u32, col: u32, file: Str) -> Self {
        Self {
            name: PackedOption::none(),
            line,
            col,
            file,
        }
    }

    /// Creates a new [`DebugInfo`] object that has all the fields
    /// filled in, including the name.
    ///
    /// This is intended to be for creating SIR where a value should have a
    /// meaningful name that is actually maintained across transformations.
    pub fn with_name(name: Str, line: u32, col: u32, file: Str) -> Self {
        Self {
            name: PackedOption::some(name),
            line,
            col,
            file,
        }
    }

    /// Returns the line in the original file that the entity came from.
    pub fn line(&self) -> u32 {
        self.line
    }

    /// Returns the column in the original file that the entity came from.
    pub fn col(&self) -> u32 {
        self.col
    }

    /// A reference to the filename. This can be resolved into a real string
    /// by using the [`StringPool`](crate::utility::StringPool) associated with
    /// the SIR module that this [`DebugInfo`] came from.
    pub fn file(&self) -> Str {
        self.file
    }

    /// A reference to a name in the IR for a value. If this is `Some(s)`, the
    /// value was given a name either in the SIR's textual form or in an IR builder.
    /// If no name is present, this value is simply unnamed and will be given a name
    /// when the SIR is printed.
    ///
    /// This can be resolved into a real string by using the [`StringPool`]
    /// associated with the SIR module that this [`DebugInfo`] came from.
    ///
    /// [`StringPool`]: crate::utility::StringPool
    pub fn name(&self) -> Option<Str> {
        self.name.expand()
    }
}

assert_eq_size!(DebugInfo, (usize, usize));
