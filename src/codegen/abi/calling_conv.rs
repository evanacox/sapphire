//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::{Architecture, Ctx, WriteableReg};
use crate::ir;

/// Models a calling convention.
///
/// This handles emitting the code to properly `call` functions, including
/// any stack alignment, parameter passing, etc.
pub trait CallingConv<Arch: Architecture> {
    /// Lowers a call instruction, handling passing arguments according to ABI rules. If
    /// the call returns a result, the result is stored into the register in `result`.
    fn lower_call(
        &self,
        call: &ir::CallInst,
        result: Option<WriteableReg>,
        context: Ctx<'_, '_, '_, '_, Arch>,
    );

    /// Lowers an indirect call instruction, handling passing arguments according to ABI rules. If
    /// the call returns a result, the result is stored into the register in `result`.
    fn lower_indirect_call(
        &self,
        call: &ir::IndirectCallInst,
        result: Option<WriteableReg>,
        context: Ctx<'_, '_, '_, '_, Arch>,
    );
}
