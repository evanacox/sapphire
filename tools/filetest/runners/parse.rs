//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::subtest::{Subtest, TestResult};
use sapphire::analysis;
use sapphire::transforms;

fn parser_output(name: &str, content: &str) -> TestResult {
    match sapphire::parse_sir(name, content) {
        Ok(module) => {
            // this also tests the verifier. Every SIR file we parse should
            // also correctly verify, anything that doesn't is a bug.
            transforms::verify_module_panic(&module);

            TestResult::Output(analysis::stringify_module(&module))
        }
        Err(err) => TestResult::CompileError(format!("{err}")),
    }
}

pub const fn parse_subtest() -> Subtest {
    Subtest::new("parse", parser_output)
}
