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
use sapphire::codegen::x86_64::X86_64Assembly;
use sapphire::codegen::{CodegenOptions, PresetBackends, PresetTargets, TargetPair};
use sapphire::transforms;

fn lsra_x86(name: &str, content: &str) -> TestResult {
    let options = CodegenOptions {
        omit_frame_pointer: !name.contains("no_omit_fp"),
    };

    let module = match sapphire::parse_sir(name, content) {
        Ok(module) => {
            // this also tests the verifier. Every SIR file we parse should
            // also correctly verify, anything that doesn't is a bug.
            transforms::verify_module_panic(&module);

            module
        }
        Err(err) => return TestResult::CompileError(err),
    };

    let target = if name.contains("3reg") {
        PresetTargets::debug_3reg(options)
    } else {
        PresetTargets::linux_x86_64(options)
    };

    TestResult::Output(PresetBackends::x86_64_unoptimized(module, target).assembly(
        X86_64Assembly::GNUIntel,
        TargetPair::X86_64Linux,
        false,
    ))
}

pub const fn lsra_x86_subtest() -> Subtest {
    Subtest::new(&["codegen/x86-64/lsra"], lsra_x86)
}
