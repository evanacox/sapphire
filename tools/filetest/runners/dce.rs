//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::subtest::{Subtest, TestResult};
use sapphire::analysis;
use sapphire::analysis::*;
use sapphire::pass::*;
use sapphire::transforms;
use sapphire::transforms::DeadCodeEliminationPass;

fn dce(name: &str, content: &str) -> TestResult {
    match sapphire::parse_sir(name, content) {
        Ok(mut module) => {
            let mut fam = FunctionAnalysisManager::default();
            fam.add_analysis(ControlFlowGraphAnalysis);
            fam.add_analysis(DominatorTreeAnalysis);

            let mut mam = ModuleAnalysisManager::default();
            mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));

            let mut mpm = ModulePassManager::new();
            mpm.add_pass(FunctionToModulePassAdapter::adapt(DeadCodeEliminationPass));

            mpm.run(&mut module, &mut mam);

            TestResult::Output(stringify_module(&module))
        }
        Err(err) => TestResult::CompileError(format!("{err}")),
    }
}

pub const fn dce_subtest() -> Subtest {
    Subtest::new("dce", dce)
}
