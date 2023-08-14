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

fn isel_greedy_x86_64(name: &str, content: &str) -> TestResult {
    let module = match sapphire::parse_sir(name, content) {
        Ok(module) => {
            // this also tests the verifier. Every SIR file we parse should
            // also correctly verify, anything that doesn't is a bug.
            transforms::verify_module_panic(&module);

            module
        }
        Err(err) => return TestResult::CompileError(err.to_string()),
    };

    let options = CodegenOptions {
        omit_frame_pointer: !name.contains("no_omit_fp"),
    };

    let target = PresetTargets::linux_x86_64(options);

    TestResult::Output(
        PresetBackends::x86_64_debug_no_reg_alloc(module, target).assembly(
            X86_64Assembly::GNUIntel,
            TargetPair::X86_64Linux,
            false,
        ),
    )
}

pub const fn isel_greedy_x86_subtest() -> Subtest {
    Subtest::new(
        &[
            "codegen/x86-64/isel",
            "codegen/x86-64/isel/arith",
            "codegen/x86-64/isel/builtins",
            "codegen/x86-64/isel/constants",
            "codegen/x86-64/isel/icmp",
            "codegen/x86-64/isel/memory",
            "codegen/x86-64/isel/phi",
            "codegen/x86-64/isel/stack",
            "codegen/x86-64/isel/system-v",
        ],
        isel_greedy_x86_64,
    )
}
