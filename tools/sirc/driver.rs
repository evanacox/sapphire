//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::options::Options;
use sapphire::analysis::*;
use sapphire::codegen::x86_64::{GreedyISel, X86_64};
use sapphire::codegen::{
    x86_64, Backend, CodegenOptions, GenericISel, PresetBackends, PresetTargets, TargetPair,
};
use sapphire::ir::Module;
use sapphire::pass::*;
use sapphire::transforms::*;
use std::fs;
use std::io;
use std::io::ErrorKind;
use std::path::{Path, PathBuf};

/// Drives compilation given a list of options
pub fn driver(options: Options) -> io::Result<()> {
    for input in options.base.inputs {
        // for now, non-utf8 path names aren't real
        let source = fs::read_to_string(&input).expect("file did not exist");
        let path = input.into_os_string().into_string().unwrap();
        let real_name = input
            .file_name()
            .expect("file somehow doesn't have a name")
            .into_os_string()
            .into_string()
            .unwrap();

        match compile_single_file(&source, &path, &real_name, &options) {
            Ok(_) => {}
            Err(_) => {
                return Err(io::Error::new(
                    ErrorKind::InvalidInput,
                    "failed to build file",
                ))
            }
        }
    }

    Ok(())
}

fn compile_single_file(source: &str, path: &str, name: &str, options: &Options) -> Result<(), ()> {
    match sapphire::parse_sir(path_string, &source) {
        Ok(module) => {
            match options.target {
                TargetPair::X86_64Linux | TargetPair::X86_64macOS | TargetPair::X86_64Windows => {
                    compile_x86_64(module, options.target, options);
                }
                TargetPair::Aarch64Linux | TargetPair::Arm64macOS | TargetPair::Arm64Windows => {
                    unimplemented!()
                }
            }

            Ok(())
        }
        Err(e) => {
            eprintln!("failed to parse: {e}");

            Err(())
        }
    }
}

fn run_passes(module: &mut Module, options: &Options, extra: &[&'static str]) {
    let mut fam = FunctionAnalysisManager::new();
    fam.add_analysis(ControlFlowGraphAnalysis);
    fam.add_analysis(DominatorTreeAnalysis);
    fam.add_analysis(DominanceFrontierAnalysis);

    let mut mam = ModuleAnalysisManager::new();
    mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));
    mam.add_analysis(ModuleStringifyAnalysis);

    let mut fpm = FunctionPassManager::new();

    for pass in options.passes.iter().chain(extra.iter()) {
        match pass.as_str() {
            "mem2reg" => fpm.add_pass(Mem2RegPass),
            "dce" => fpm.add_pass(DeadCodeEliminationPass),
            "gvn" => fpm.add_pass(GlobalValueNumberingPass),
            "simplifyinst" => fpm.add_pass(SimplifyInstPass),
            "split-crit-edges" => fpm.add_pass(SplitCriticalEdges),
            _ => {
                unreachable!()
            }
        }
    }

    let mut mpm = ModulePassManager::new();

    if options.verify {
        mpm.add_pass(VerifyModulePass);
    }

    mpm.add_pass(FunctionToModulePassAdapter::adapt(fpm));

    // no reason to verify a second time if we didn't change anything
    if options.verify && !options.passes.is_empty() {
        mpm.add_pass(VerifyModulePass);
    }

    mpm.run(module, &mut mam);
}

fn compile_x86_64(mut module: Module, pair: TargetPair, options: &Options) {
    // the x86-64 backend requires split-crit-edges before lowering
    run_passes(&mut module, options, &["split-crit-edges"]);

    let mut target = match pair {
        TargetPair::X86_64Linux => PresetTargets::linux_x86_64(options.codegen),
        TargetPair::X86_64macOS => PresetTargets::mac_os_x86_64(options.codegen),
        TargetPair::X86_64Windows => PresetTargets::windows_x86_64(options.codegen),
        _ => unreachable!(),
    };

    let mir = GenericISel::<X86_64, GreedyISel>::lower(&mut target, &module, options.codegen);
    let backend = Backend::<X86_64, x86_64::Emit>::from_mir(mir);

    println!("{}", backend.assembly(X86_64Assembly::GNUIntel));
}
