//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::x86_64::sysv::{SystemVCallingConv, SystemVStackFrame};
use crate::codegen::x86_64::win64::{WindowsX64CallingConv, WindowsX64StackFrame};
use crate::codegen::x86_64::X86_64;
use crate::codegen::{PReg, Target, TypeLayout, ABI};
use crate::ir::{Array, Struct, Type, TypePool, UType};
use smallvec::SmallVec;
use std::iter;

/// The x86-64 System V ABI.
///
/// This is the dominant ABI for Linux, macOS, BSDs and other *nix platforms
/// on the x86-64 platform.
pub struct SystemV;

#[allow(clippy::upper_case_acronyms)]
#[repr(u8)]
#[derive(Copy, Clone)]
enum SystemVTypeClass {
    Integer,
    SSE,
    SSEUp,
    X87,
    X87Up,
    ComplexX87,
    Memory,
    NoClass,
}

impl SystemV {
    fn classify_type(pool: &TypePool, ty: Type, target: &Target<X86_64>) -> SystemVTypeClass {
        match ty.unpack() {
            UType::Int(_) | UType::Bool(_) | UType::Ptr(_) => SystemVTypeClass::Integer,
            UType::Float(_) => SystemVTypeClass::SSE,
            UType::Struct(structure) => Self::classify_struct(pool, ty, structure, target),
            UType::Array(array) => Self::classify_array(pool, ty, array, target),
        }
    }

    fn classify_array(
        pool: &TypePool,
        ty: Type,
        array: Array,
        target: &Target<X86_64>,
    ) -> SystemVTypeClass {
        let layout = target.layout_of(ty);

        if layout.size() > 64 {
            return SystemVTypeClass::Memory;
        }

        todo!()
    }

    fn classify_struct(
        pool: &TypePool,
        ty: Type,
        structure: Struct,
        target: &Target<X86_64>,
    ) -> SystemVTypeClass {
        let layout = target.layout_of(ty);

        if layout.size() > 64 {
            return SystemVTypeClass::Memory;
        }

        //
        // possible algo:
        //
        // set up an array of bytes, each byte with classification
        // deal with 8 at a time
        //
        //

        let members = structure.members(pool);

        // initialize our list of eight-bytes to NO_CLASS
        let words = SmallVec::<[SystemVTypeClass; 16]>::from_iter(
            iter::repeat(SystemVTypeClass::NoClass).take(layout.size() as usize),
        );

        for i in 0..(members.len() - 1) {}

        todo!()
    }
}

impl ABI<X86_64> for SystemV {
    type Frame = SystemVStackFrame;

    type CallingConv = SystemVCallingConv;

    fn callee_preserved() -> &'static [PReg] {
        todo!()
    }

    fn caller_preserved() -> &'static [PReg] {
        todo!()
    }

    fn frame_pointer() -> PReg {
        todo!()
    }

    fn stack_pointer() -> PReg {
        todo!()
    }

    fn stack_alignment() -> u64 {
        todo!()
    }

    fn can_pass_in_registers(pool: &TypePool, ty: Type, layout: TypeLayout) -> bool {
        todo!()
    }
}

/// The x64 Windows ABI
///
/// This is the dominant ABI for x86-64 on Windows.
pub struct WindowsX64;

impl ABI<X86_64> for WindowsX64 {
    type Frame = WindowsX64StackFrame;

    type CallingConv = WindowsX64CallingConv;

    fn callee_preserved() -> &'static [PReg] {
        todo!()
    }

    fn caller_preserved() -> &'static [PReg] {
        todo!()
    }

    fn frame_pointer() -> PReg {
        todo!()
    }

    fn stack_pointer() -> PReg {
        todo!()
    }

    fn stack_alignment() -> u64 {
        todo!()
    }

    fn can_pass_in_registers(pool: &TypePool, ty: Type, layout: TypeLayout) -> bool {
        todo!()
    }
}
