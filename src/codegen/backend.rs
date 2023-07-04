//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::codegen::x86_64::{GreedyISel, SystemV, X86_64};
use crate::codegen::{x86_64, GenericISel, PresetTargets};
use crate::codegen::{Architecture, Emitter, MIRModule, MachInst};
use crate::ir::Module;
use crate::pass::*;
use crate::transforms::*;
use std::marker::PhantomData;

/// A generic backend using a specified emitter. The [`Backend`] doesn't directly
/// perform instruction selection by itself, that is done during the creation
/// of the [`Backend`] instance.
pub struct Backend<Arch, Inst, Emit>
where
    Arch: Architecture,
    Inst: MachInst<Arch>,
    Emit: Emitter<Arch, Inst>,
{
    mir: MIRModule<Arch, Inst>,
    _unused: PhantomData<fn() -> Emit>,
}

impl<Arch, Inst, Emit> Backend<Arch, Inst, Emit>
where
    Arch: Architecture,
    Inst: MachInst<Arch>,
    Emit: Emitter<Arch, Inst>,
{
    /// Emits assembly in a format specified by the emitter, returning
    /// a string that can be written to a file
    pub fn assembly(&self, format: Emit::AssemblyFormat) -> String {
        Emit::assembly(&self.mir, format)
    }

    /// Emits object code in a format specified by the emitter, returning
    /// a byte array that can be written to a file
    pub fn object(&self, format: Emit::ObjectCodeFormat) -> Vec<u8> {
        Emit::object(&self.mir, format)
    }
}

/// A set of pre-made backend pipelines for various architectures
/// and ABIs, made for convenience.
pub struct PresetBackends;

impl PresetBackends {
    /// An 'optimized' pipeline preset for x86-64 on the System V ABI.
    pub fn x86_64_sys_v_optimized(
        mut module: Module,
    ) -> Backend<X86_64, x86_64::Inst, x86_64::Emit> {
        let fam = FunctionAnalysisManager::default();
        let mut mam = ModuleAnalysisManager::new();
        let mut fpm = FunctionPassManager::new();
        let mut mpm = ModulePassManager::new();

        mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));

        fpm.add_pass(Mem2RegPass);
        fpm.add_pass(DeadCodeEliminationPass);
        fpm.add_pass(SimplifyInstPass);
        fpm.add_pass(GlobalValueNumberingPass);
        fpm.add_pass(SimplifyInstPass);
        fpm.add_pass(DeadCodeEliminationPass);

        // split-crit-edges must happen at the end so that SSA deconstruction can happen
        fpm.add_pass(SplitCriticalEdges);

        mpm.add_pass(FunctionToModulePassAdapter::adapt(fpm));
        mpm.run(&mut module, &mut mam);

        let mut target = PresetTargets::sys_v();
        let module = GenericISel::<_, _, _, GreedyISel<SystemV>>::lower(&mut target, &module);

        Backend {
            mir: module,
            _unused: PhantomData::default(),
        }
    }

    /// An "unoptimized" pipeline for x86-64 on the System V ABI.
    pub fn x86_64_sys_v_unoptimized(
        mut module: Module,
    ) -> Backend<X86_64, x86_64::Inst, x86_64::Emit> {
        let fam = FunctionAnalysisManager::default();
        let mut mam = ModuleAnalysisManager::new();
        let mut fpm = FunctionPassManager::new();
        let mut mpm = ModulePassManager::new();

        mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));

        // split-crit-edges must happen at the end so that SSA deconstruction can happen
        fpm.add_pass(SplitCriticalEdges);

        mpm.add_pass(FunctionToModulePassAdapter::adapt(fpm));
        mpm.run(&mut module, &mut mam);

        #[cfg(playground)]
        crate::analysis::print_module(&module);

        let mut target = PresetTargets::sys_v();
        let module = GenericISel::<_, _, _, GreedyISel<SystemV>>::lower(&mut target, &module);

        Backend {
            mir: module,
            _unused: PhantomData::default(),
        }
    }
}
