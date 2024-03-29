//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

mod discovery;
mod display;
mod runner;
mod runners;
mod subtest;
mod testcase;

use crate::runner::{run_all, run_subtest};
use bpaf::Parser;
use sapphire::cli;

fn subtest() -> impl Parser<Option<String>> {
    bpaf::long("subtest")
        .help("the subtest to run, is name of a subdir of 'tests/'")
        .argument::<String>("NAME")
        .optional()
}

fn main() {
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

        std::process::exit(1);
    }

    let result = match subtest {
        Some(s) => run_subtest(&s, jobs),
        None => run_all(jobs),
    };

    if result.is_err() {
        std::process::exit(1);
    }
}

#[test]
fn test_parse() {
    assert!(matches!(run_subtest("parse", Some(1)), Ok(())));
}

#[test]
fn test_domtree() {
    assert!(matches!(run_subtest("domtree", Some(1)), Ok(())))
}

#[test]
fn test_mem2reg() {
    assert!(matches!(run_subtest("mem2reg", Some(1)), Ok(())));
}

#[test]
fn test_dce() {
    assert!(matches!(run_subtest("dce", Some(1)), Ok(())));
}

#[test]
fn test_gvn() {
    assert!(matches!(run_subtest("gvn", Some(1)), Ok(())));
}

#[test]
fn test_simplifyinst() {
    assert!(matches!(run_subtest("simplifyinst", Some(1)), Ok(())))
}

#[test]
fn test_isel_x86() {
    assert!(matches!(run_subtest("isel-x86", Some(1)), Ok(())))
}

#[test]
fn test_lsra_x86() {
    assert!(matches!(run_subtest("lsra-x86", Some(1)), Ok(())))
}
