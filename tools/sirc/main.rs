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
use sapphire::cli;
use sapphire::ir::Module;
use sapphire::pass::*;
use sapphire::transforms::*;
use std::fs;

fn run_pass(mut module: Module) {
    let mut fam = FunctionAnalysisManager::new();
    fam.add_analysis(ControlFlowGraphAnalysis);
    fam.add_analysis(DominatorTreeAnalysis);
    fam.add_analysis(DominanceFrontierAnalysis);

    let mut mam = ModuleAnalysisManager::new();
    mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));
    mam.add_analysis(ModuleStringifyAnalysis);

    let mut fpm = FunctionPassManager::new();
    fpm.add_pass(Mem2RegPass);
    fpm.add_pass(DeadCodeEliminationPass);

    let mut mpm = ModulePassManager::new();
    mpm.add_pass(FunctionToModulePassAdapter::adapt(fpm));

    print_module(&module);

    mpm.run(&mut module, &mut mam);

    print_module(&module);
}

fn main() {
    let (_, base) = cli::tool_with(
        "static compiler for Sapphire IR",
        "Usage: sirc [options] <input ir>",
        cli::emit_machine_format(),
    )
    .run();

    for input in base.inputs {
        // for now, non-utf8 path names aren't real
        let source = fs::read_to_string(&input).expect("file did not exist");
        let filename = input.into_os_string().into_string().unwrap();

        match sapphire::parse_sir(&filename, &source) {
            Ok(module) => run_pass(module),
            Err(e) => {
                eprintln!("failed to parse: {e}");
            }
        }
    }
}
