//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::x86_64::{GreedyISel, X86_64};
use crate::codegen::{
    x86_64, GenericISel, LinearScanRegAlloc, RegisterAllocator, Rewriter, Target, TargetPair,
};
use crate::codegen::{Architecture, Emitter, MIRModule};
use crate::ir::Module;
use crate::pass::*;
use crate::transforms::*;
use std::marker::PhantomData;

/// A generic backend using a specified emitter. The [`Backend`] doesn't directly
/// perform instruction selection by itself, that is done during the creation
/// of the [`Backend`] instance.
pub struct Backend<Arch, Emit>
where
    Arch: Architecture,
    Emit: Emitter<Arch>,
{
    mir: MIRModule<Arch::Inst>,
    _unused: PhantomData<fn() -> Emit>,
}

impl<Arch, Emit> Backend<Arch, Emit>
where
    Arch: Architecture,
    Emit: Emitter<Arch>,
{
    /// Creates a [`Backend`] from a MIR module.
    pub fn from_mir(mir: MIRModule<Arch::Inst>) -> Self {
        Backend {
            mir,
            _unused: PhantomData::default(),
        }
    }

    /// Emits assembly in a format specified by the emitter, returning
    /// a string that can be written to a file
    #[inline]
    pub fn assembly(
        &self,
        format: Emit::AssemblyFormat,
        target: TargetPair,
        fixed_interval_comments: bool,
    ) -> String {
        Emit::assembly(&self.mir, format, target, fixed_interval_comments)
    }

    /// Emits object code in a format specified by the emitter, returning
    /// a byte array that can be written to a file
    #[inline]
    pub fn object(&self, format: Emit::ObjectCodeFormat) -> Vec<u8> {
        Emit::object(&self.mir, format)
    }
}

fn allocate<Arch, Alloc>(mut mir: MIRModule<Arch::Inst>) -> MIRModule<Arch::Inst>
where
    Arch: Architecture,
    Alloc: RegisterAllocator<Arch>,
{
    for (func, frame) in mir.functions_mut() {
        let allocation = Alloc::allocate(func, frame.as_mut());
        let rewriter = Rewriter::with_allocation(allocation);

        rewriter.rewrite(func, frame.as_ref());
    }

    mir
}

/// A set of pre-made backend pipelines for various architectures
/// and ABIs, made for convenience.
pub struct PresetBackends;

impl PresetBackends {
    /// An 'optimized' pipeline preset for x86-64 with a given target
    pub fn x86_64_optimized(
        mut module: Module,
        mut target: Target<X86_64>,
    ) -> Backend<X86_64, x86_64::Emit> {
        let fam = FunctionAnalysisManager::default();
        let mut mam = ModuleAnalysisManager::new();
        let mut fpm = FunctionPassManager::new();
        let mut mpm = ModulePassManager::new();

        mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));

        fpm.add_pass(Mem2RegPass);
        fpm.add_pass(AggressiveDCEPass);
        fpm.add_pass(SimplifyInstPass);
        fpm.add_pass(GVNPass);
        fpm.add_pass(SimplifyInstPass);
        fpm.add_pass(AggressiveDCEPass);

        // split-crit-edges must happen at the end so that SSA deconstruction can happen
        fpm.add_pass(SplitCriticalEdgesPass);

        mpm.add_pass(FunctionToModulePassAdapter::adapt(fpm));
        mpm.run(&mut module, &mut mam);

        let mir = GenericISel::<X86_64, GreedyISel>::lower(&mut target, &module);

        Backend {
            mir: allocate::<X86_64, LinearScanRegAlloc<'_>>(mir),
            _unused: PhantomData::default(),
        }
    }

    /// An "unoptimized" pipeline for x86-64 on the System V ABI.
    pub fn x86_64_unoptimized(
        mut module: Module,
        mut target: Target<X86_64>,
    ) -> Backend<X86_64, x86_64::Emit> {
        let fam = FunctionAnalysisManager::default();
        let mut mam = ModuleAnalysisManager::new();
        let mut fpm = FunctionPassManager::new();
        let mut mpm = ModulePassManager::new();

        mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));

        // split-crit-edges must happen at the end so that SSA deconstruction can happen
        fpm.add_pass(SplitCriticalEdgesPass);

        mpm.add_pass(FunctionToModulePassAdapter::adapt(fpm));
        mpm.run(&mut module, &mut mam);

        let mir = GenericISel::<X86_64, GreedyISel>::lower(&mut target, &module);

        Backend {
            mir: allocate::<X86_64, LinearScanRegAlloc<'_>>(mir),
            _unused: PhantomData::default(),
        }
    }

    /// An "unoptimized" pipeline that doesn't actually perform register allocation
    pub fn x86_64_debug_no_reg_alloc(
        mut module: Module,
        mut target: Target<X86_64>,
    ) -> Backend<X86_64, x86_64::Emit> {
        let fam = FunctionAnalysisManager::default();
        let mut mam = ModuleAnalysisManager::new();
        let mut fpm = FunctionPassManager::new();
        let mut mpm = ModulePassManager::new();

        mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));

        // split-crit-edges must happen at the end so that SSA deconstruction can happen
        fpm.add_pass(SplitCriticalEdgesPass);

        mpm.add_pass(FunctionToModulePassAdapter::adapt(fpm));
        mpm.run(&mut module, &mut mam);

        Backend {
            mir: GenericISel::<X86_64, GreedyISel>::lower(&mut target, &module),
            _unused: PhantomData::default(),
        }
    }
}
