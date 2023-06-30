//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::common::STANDARD_64_BIT_LAYOUT;
use crate::codegen::{Architecture, CPUArch, PReg, TypeLayout};

const X86_64_REGS: [PReg; 33] = [
    PReg::int(0),    // rax
    PReg::int(1),    // rcx
    PReg::int(2),    // rdx
    PReg::int(3),    // rbx
    PReg::int(4),    // rsi
    PReg::int(5),    // rdi
    PReg::int(6),    // rsp
    PReg::int(7),    // rbp
    PReg::int(8),    // r8
    PReg::int(9),    // r9
    PReg::int(10),   // r10
    PReg::int(11),   // r11
    PReg::int(12),   // r12
    PReg::int(13),   // r13
    PReg::int(14),   // r14
    PReg::int(15),   // r15
    PReg::int(16),   // rip
    PReg::float(0),  // xmm0
    PReg::float(1),  // xmm1
    PReg::float(2),  // xmm2
    PReg::float(3),  // xmm3
    PReg::float(4),  // xmm4
    PReg::float(5),  // xmm5
    PReg::float(6),  // xmm6
    PReg::float(7),  // xmm7
    PReg::float(8),  // xmm8
    PReg::float(9),  // xmm9
    PReg::float(10), // xmm10
    PReg::float(11), // xmm11
    PReg::float(12), // xmm12
    PReg::float(13), // xmm13
    PReg::float(14), // xmm14
    PReg::float(15), // xmm15
];

/// A target for a generic x86_64 CPU.
#[derive(Default)]
pub struct X86_64;

impl X86_64 {
    /// A [`PReg`] referring to `rax`
    pub const RAX: PReg = X86_64_REGS[0];

    /// A [`PReg`] referring to `rcx`
    pub const RCX: PReg = X86_64_REGS[1];

    /// A [`PReg`] referring to `rdx`
    pub const RDX: PReg = X86_64_REGS[2];

    /// A [`PReg`] referring to `rbx`
    pub const RBX: PReg = X86_64_REGS[3];

    /// A [`PReg`] referring to `rsi`
    pub const RSI: PReg = X86_64_REGS[4];

    /// A [`PReg`] referring to `rdi`
    pub const RDI: PReg = X86_64_REGS[5];

    /// A [`PReg`] referring to `rsp`
    pub const RSP: PReg = X86_64_REGS[6];

    /// A [`PReg`] referring to `rbp`
    pub const RBP: PReg = X86_64_REGS[7];

    /// A [`PReg`] referring to `r8`
    pub const R8: PReg = X86_64_REGS[8];

    /// A [`PReg`] referring to `r9`
    pub const R9: PReg = X86_64_REGS[9];

    /// A [`PReg`] referring to `r10`
    pub const R10: PReg = X86_64_REGS[10];

    /// A [`PReg`] referring to `r11`
    pub const R11: PReg = X86_64_REGS[11];

    /// A [`PReg`] referring to `r12`
    pub const R12: PReg = X86_64_REGS[12];

    /// A [`PReg`] referring to `r13`
    pub const R13: PReg = X86_64_REGS[13];

    /// A [`PReg`] referring to `r14`
    pub const R14: PReg = X86_64_REGS[14];

    /// A [`PReg`] referring to `r15`
    pub const R15: PReg = X86_64_REGS[15];

    /// A [`PReg`] referring to `rip`
    pub const RIP: PReg = X86_64_REGS[16];

    /// Gets a [`PReg`] referring to the `n`th `xmmN` floating-point registers.
    pub const fn xmm(n: usize) -> PReg {
        X86_64_REGS[17 + n]
    }
}

impl Architecture for X86_64 {
    #[inline]
    fn cpu() -> CPUArch {
        CPUArch::X86_64
    }

    #[inline]
    fn bool_layout() -> TypeLayout {
        STANDARD_64_BIT_LAYOUT[0]
    }

    #[inline]
    fn ptr_layout() -> TypeLayout {
        STANDARD_64_BIT_LAYOUT[1]
    }

    #[inline]
    fn i8_layout() -> TypeLayout {
        STANDARD_64_BIT_LAYOUT[2]
    }

    #[inline]
    fn i16_layout() -> TypeLayout {
        STANDARD_64_BIT_LAYOUT[3]
    }

    #[inline]
    fn i32_layout() -> TypeLayout {
        STANDARD_64_BIT_LAYOUT[4]
    }

    #[inline]
    fn i64_layout() -> TypeLayout {
        STANDARD_64_BIT_LAYOUT[5]
    }

    #[inline]
    fn f32_layout() -> TypeLayout {
        STANDARD_64_BIT_LAYOUT[6]
    }

    #[inline]
    fn f64_layout() -> TypeLayout {
        STANDARD_64_BIT_LAYOUT[7]
    }

    #[inline]
    fn physical_regs() -> &'static [PReg] {
        &X86_64_REGS
    }

    #[inline]
    fn instruction_pointer() -> PReg {
        X86_64::RIP
    }
}

/// Information about the stack frame of a function
pub struct FrameInfo {
    current: usize,
}
