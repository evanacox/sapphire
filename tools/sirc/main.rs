//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use sapphire::analysis::*;
use sapphire::cli::{emit_machine_format, passes, tool_with};
use sapphire::codegen::x86_64::X86_64Assembly;
use sapphire::codegen::PresetBackends;
use sapphire::ir::Module;
use sapphire::pass::*;
use sapphire::transforms::*;
use std::fs;

fn run_passes(module: &mut Module, passes: &[String]) {
    let mut fam = FunctionAnalysisManager::new();
    fam.add_analysis(ControlFlowGraphAnalysis);
    fam.add_analysis(DominatorTreeAnalysis);
    fam.add_analysis(DominanceFrontierAnalysis);

    let mut mam = ModuleAnalysisManager::new();
    mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));
    mam.add_analysis(ModuleStringifyAnalysis);

    let mut fpm = FunctionPassManager::new();

    for pass in passes {
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
    mpm.add_pass(VerifyModulePass);
    mpm.add_pass(FunctionToModulePassAdapter::adapt(fpm));
    mpm.add_pass(VerifyModulePass);

    // print_module(&module);

    mpm.run(module, &mut mam);

    // print_module(&module);
}

fn main() {
    let ((_, passes), base) = tool_with(
        "static compiler for Sapphire IR",
        "Usage: sirc [options] <input ir>",
        bpaf::construct!(emit_machine_format(), passes()),
    )
    .run();

    for input in base.inputs {
        // for now, non-utf8 path names aren't real
        let source = fs::read_to_string(&input).expect("file did not exist");
        let filename = input.into_os_string().into_string().unwrap();

        match sapphire::parse_sir(&filename, &source) {
            Ok(mut module) => {
                run_passes(&mut module, &passes);

                let backend = PresetBackends::x86_64_sys_v_unoptimized(module);

                println!("{}", backend.assembly(X86_64Assembly::GNUIntel));
            }
            Err(e) => {
                eprintln!("failed to parse: {e}");
            }
        }
    }
}
