//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

mod discovery;
mod parse;
mod runner;
mod subtest;

use crate::runner::{run_all, run_subtest};
use bpaf::Parser;
use sapphire::cli;
use std::process::ExitCode;

fn subtest() -> impl Parser<Option<String>> {
    bpaf::long("subtest")
        .help("the subtest to run, is name of a subdir of 'tests/'")
        .argument::<String>("NAME")
        .optional()
}

fn main() -> ExitCode {
    #[cfg(windows)]
    ansi_term::enable_ansi_support().expect("unable to enable ANSI");

    let jobs = cli::jobs();
    let subtest = subtest();
    let ((subtest, jobs), options) = cli::tool_with(
        "file-driven test runner for Sapphire",
        "filetest [--subtest <NAME>]",
        bpaf::construct!(subtest, jobs),
    )
    .run();

    if !options.inputs.is_empty() {
        eprintln!("expected file list to be empty!");

        return ExitCode::from(1);
    }

    let result = match subtest {
        Some(s) => run_subtest(&s, jobs),
        None => run_all(jobs),
    };

    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(_) => ExitCode::from(1),
    }
}

#[test]
fn test_parse() {
    assert!(matches!(run_subtest("parse", Some(2)), Ok(())));
}
