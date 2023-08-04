//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

/// A set of detailed codegen configuration options that are provided
/// during the lowering process.
///
/// This effectively models the `-fthing` argument pattern in GCC-like
/// compilers.
#[derive(Copy, Clone, Debug)]
pub struct CodegenOptions {
    /// Whether to attempt to omit the frame pointer, if possible on the target.
    ///
    /// This is not a binding requirement to always omit, some functions (most
    /// notably the ones that use `alloca`) must use the frame pointer.
    pub omit_frame_pointer: bool,
}

#[allow(clippy::derivable_impls)]
impl Default for CodegenOptions {
    fn default() -> Self {
        Self {
            omit_frame_pointer: false,
        }
    }
}
