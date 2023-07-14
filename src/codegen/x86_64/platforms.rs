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
use crate::codegen::x86_64::win64::WindowsX64CallingConv;
use crate::codegen::x86_64::X86_64;
use crate::codegen::{CallingConv, Platform, StackFrame, Target};
use crate::ir::{Cursor, FuncView, Function};

pub(in crate::codegen::x86_64) const SYS_V_CC: SystemVCallingConv = SystemVCallingConv;

pub(in crate::codegen::x86_64) const WINDOWS_X64_CC: WindowsX64CallingConv = WindowsX64CallingConv;

/// A platform representing (typical) Linux-based operating systems.
///
/// This uses the System V ABI.
#[derive(Debug)]
pub struct LinuxX86_64;

#[inline]
fn sys_v(func: &Function, target: &Target<X86_64>) -> Box<dyn StackFrame<X86_64>> {
    let sig = func.signature();
    let view = FuncView::over(func);
    let params = view.block_params(view.entry_block().unwrap());
    let meta = func.compute_metadata().unwrap();
    let frame = SystemVStackFrame::new(func, target);

    Box::new(frame)
}

impl Platform<X86_64> for LinuxX86_64 {
    fn default_calling_convention(&self) -> &'static dyn CallingConv<X86_64> {
        &SYS_V_CC
    }

    fn default_stack_frame(
        &self,
        func: &Function,
        target: &Target<X86_64>,
    ) -> Box<dyn StackFrame<X86_64>> {
        sys_v(func, target)
    }
}

/// A platform representing the (x86-64 variation of) the macOS operating systems.
///
/// This uses the System V ABI.
#[derive(Debug)]
pub struct MacOSX86_64;

impl Platform<X86_64> for MacOSX86_64 {
    fn default_calling_convention(&self) -> &'static dyn CallingConv<X86_64> {
        &SYS_V_CC
    }

    fn default_stack_frame(
        &self,
        func: &Function,
        target: &Target<X86_64>,
    ) -> Box<dyn StackFrame<X86_64>> {
        sys_v(func, target)
    }
}

/// A platform representing the (x86-64 variation of) the Windows operating system.
///
/// This uses the Windows x64 calling convention, and follows the Windows x64 ABI.
#[derive(Debug)]
pub struct WindowsX86_64;

impl Platform<X86_64> for WindowsX86_64 {
    fn default_calling_convention(&self) -> &'static dyn CallingConv<X86_64> {
        &WINDOWS_X64_CC
    }

    fn default_stack_frame(
        &self,
        func: &Function,
        target: &Target<X86_64>,
    ) -> Box<dyn StackFrame<X86_64>> {
        todo!()
    }
}
