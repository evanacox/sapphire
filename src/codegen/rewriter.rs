//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

/// Performs the final phase of codegen, rewriting register-allocated x86-64
/// MIR to be fully valid x86-64 instructions that are ready to emit.
///
/// The main tasks being performed are these:
///
/// 1. Rewriting instructions to use hardware registers (based on register allocation)
/// 2. Emitting any necessary prologue/epilogue code
/// 3. Rewriting stack accesses to have correct offsets (since register allocation
///    can spill registers and that will change any stack offsets relative to the
///    stack pointer)
/// 3. Eliminating redundant `mov` instructions (e.g. `mov rax, rax`)
pub struct Rewriter {
    //
}

impl Rewriter {
    //
}
