//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::options::{OptLevel, Options, RegAlloc};
use sapphire::analysis::*;
use sapphire::codegen::x86_64::{GreedyISel, X86_64Assembly, X86_64};
use sapphire::codegen::{
    x86_64, Backend, GenericISel, LinearScanRegAlloc, PresetTargets, RegisterAllocator, Rewriter,
    StackRegAlloc, TargetPair,
};
use sapphire::ir::Module;
use sapphire::pass::*;
use sapphire::transforms::*;
use std::fs;
use std::io;
use std::io::ErrorKind;
use std::path::PathBuf;

/// Drives compilation given a list of options
pub fn driver(options: Options) -> io::Result<()> {
    for input in options.base.inputs.iter() {
        // for now, non-utf8 path names aren't real
        let source = fs::read_to_string(input).expect("file did not exist");
        let path = input.as_os_str().to_owned().into_string().unwrap();

        if let Err(()) = compile_single_file(&source, &path, &options) {
            return Err(io::Error::new(
                ErrorKind::InvalidInput,
                "failed to build file",
            ));
        }
    }

    Ok(())
}

fn compile_single_file(source: &str, path: &str, options: &Options) -> Result<(), ()> {
    match sapphire::parse_sir(path, source) {
        Ok(module) => {
            let asm = match options.target {
                TargetPair::X86_64Linux
                | TargetPair::X86_64macOS
                | TargetPair::X86_64Windows
                | TargetPair::Debug3Reg => compile_x86_64(module, options.target, options),
                TargetPair::Aarch64Linux | TargetPair::Arm64macOS | TargetPair::Arm64Windows => {
                    panic!(
                        "native arm codegen is not implemented, specify `--target=x86_64-{{os}}`"
                    )
                }
            };

            if options.print {
                println!("{asm}");
            } else {
                let output = if let Some(path) = &options.base.output {
                    path.clone()
                } else {
                    let mut buf = PathBuf::from(path);

                    buf.set_extension("s");

                    buf
                };

                let err = format!("unable to write output to file `{}`", output.display());

                fs::write(output, asm).expect(&err)
            }

            Ok(())
        }
        Err(e) => {
            eprintln!("failed to parse: {e}");

            Err(())
        }
    }
}

fn run_passes(
    module: &mut Module,
    options: &Options,
    fn_extra: impl FnOnce(&mut FunctionPassManager),
    module_extra: impl FnOnce(&mut ModulePassManager),
) {
    let mut fam = FunctionAnalysisManager::new();
    fam.add_analysis(ControlFlowGraphAnalysis);
    fam.add_analysis(DominatorTreeAnalysis);
    fam.add_analysis(DominanceFrontierAnalysis);

    let mut mam = ModuleAnalysisManager::new();
    mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));
    mam.add_analysis(ModuleStringifyAnalysis);

    let mut fpm = FunctionPassManager::default();

    if options.opt == OptLevel::Release {
        fpm.add_pass(Mem2RegPass);

        for _ in 0..2 {
            fpm.add_pass(SimplifyInstPass);
            fpm.add_pass(GVNPass);
            fpm.add_pass(AggressiveDCEPass);
        }
    }

    fn_extra(&mut fpm);

    let mut mpm = ModulePassManager::new();

    if options.verify {
        mpm.add_pass(VerifyModulePass);
    }

    mpm.add_pass(FunctionToModulePassAdapter::adapt(fpm));

    module_extra(&mut mpm);

    // no reason to verify a second time if we didn't change anything
    if options.verify {
        mpm.add_pass(VerifyModulePass);
    }

    mpm.run(module, &mut mam);
}

fn compile_x86_64(mut module: Module, pair: TargetPair, options: &Options) -> String {
    // the x86-64 backend requires split-crit-edges before lowering
    run_passes(
        &mut module,
        options,
        |fpm| fpm.add_pass(SplitCriticalEdgesPass),
        |_| {},
    );

    let mut target = match pair {
        TargetPair::X86_64Linux => PresetTargets::linux_x86_64(options.codegen),
        TargetPair::X86_64macOS => PresetTargets::mac_os_x86_64(),
        TargetPair::X86_64Windows => PresetTargets::windows_x86_64(options.codegen),
        TargetPair::Debug3Reg => PresetTargets::debug_3reg(options.codegen),
        _ => unreachable!(),
    };

    let mut mir = GenericISel::<X86_64, GreedyISel>::lower(&mut target, &module);

    if options.reg_alloc != RegAlloc::None {
        for (func, frame) in mir.functions_mut() {
            let allocation = match options.reg_alloc {
                RegAlloc::Stack => StackRegAlloc::allocate(func, frame.as_mut()),
                RegAlloc::Linear => LinearScanRegAlloc::allocate(func, frame.as_mut()),
                _ => todo!(),
            };

            Rewriter::with_allocation(allocation).rewrite(func, frame.as_mut());
        }
    }

    let backend = Backend::<X86_64, x86_64::Emit>::from_mir(mir);

    let output = match options.x86_64_asm {
        Some(asm) => asm,
        None => match pair {
            TargetPair::X86_64Linux => X86_64Assembly::GNU,
            TargetPair::X86_64macOS => X86_64Assembly::GNUIntel,
            TargetPair::X86_64Windows => X86_64Assembly::MASM,
            _ => unreachable!(),
        },
    };

    backend.assembly(output, pair, options.fixed_intervals)
}
