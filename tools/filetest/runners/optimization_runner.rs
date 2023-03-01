//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

macro_rules! runner_for_opt {
    ($name:ident, $opt:expr) => {
        fn $name(name: &str, content: &str) -> crate::subtest::TestResult {
            use crate::subtest::TestResult;
            use ::sapphire::analysis::*;
            use ::sapphire::pass::*;
            use ::sapphire::transforms;
            use ::sapphire::transforms::VerifyModulePass;

            match ::sapphire::parse_sir(name, content) {
                Ok(mut module) => {
                    transforms::verify_module_panic(&module);

                    let mut fam = FunctionAnalysisManager::default();
                    fam.add_analysis(ControlFlowGraphAnalysis);
                    fam.add_analysis(DominatorTreeAnalysis);
                    fam.add_analysis(DominanceFrontierAnalysis);

                    let mut mam = ModuleAnalysisManager::default();
                    mam.add_analysis(FunctionAnalysisManagerModuleProxy::wrap(fam));

                    let mut mpm = ModulePassManager::new();
                    mpm.add_pass($opt);
                    mpm.add_pass(VerifyModulePass);

                    mpm.run(&mut module, &mut mam);

                    TestResult::Output(stringify_module(&module))
                }
                Err(err) => TestResult::CompileError(format!("{err}")),
            }
        }
    };
}

pub(crate) use runner_for_opt;
