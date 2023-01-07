//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::subtest::{Subtest, TestFailure};
use sapphire::analysis;

fn test_parser(file: &str, content: &str) -> Option<TestFailure> {
    let result = match sapphire::parse_sir(file, content) {
        Ok(module) => {
            let got = analysis::stringify_module(&module);

            if got == content {
                None
            } else {
                Some(TestFailure::Diff {
                    expected: content.to_owned(),
                    got,
                })
            }
        }
        Err(err) => Some(TestFailure::CompileError(format!("{err}"))),
    };

    if file.ends_with(".pass.sir") {
        // only get None if the contents are identical, as we expect
        return result;
    }

    debug_assert!(file.ends_with(".fail.sir"));

    match result {
        // either way we failed here, this is for .fail tests and we didnt get a parse error
        Some(TestFailure::Diff { .. }) | None => Some(TestFailure::LackOfCompileError),
        // expected
        Some(TestFailure::CompileError(_)) => None,
        // ??
        _ => unreachable!(),
    }
}

pub const fn parse_subtest() -> Subtest {
    Subtest::new("parse", test_parser)
}
