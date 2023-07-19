//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::{Architecture, MIRModule, TargetPair};

/// An emitter that can emit different formats from a given type of [`MachInst`](crate::codegen::MachInst).
///
/// This is divided into two main categories, assembly output and object code
/// output.
pub trait Emitter<Arch: Architecture>: Sized {
    /// Different types of assembly, if supported by the emitter. This should be used
    /// for e.g. different assembly dialects.
    type AssemblyFormat;

    /// Different types of object code output, if supported by the emitter. This should
    /// be used for e.g. different file formats.
    type ObjectCodeFormat;

    /// Emits assembly in a format specified by the emitter, returning a string
    /// that can be written to a file or printed.
    ///
    /// Note that `fixed_interval_comments` only works when regalloc has not been done.
    fn assembly(
        module: &MIRModule<Arch::Inst>,
        format: Self::AssemblyFormat,
        target: TargetPair,
        fixed_interval_comments: bool,
    ) -> String;

    /// Emits object code in a format specified by the emitter, returning
    /// a byte buffer containing the correctly-formatted object code that can
    /// be written to a file.
    fn object(module: &MIRModule<Arch::Inst>, format: Self::ObjectCodeFormat) -> Vec<u8>;
}
