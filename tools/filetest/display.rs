//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::discovery::cases_in_subdir;
use crate::subtest::{Subtest, TestDetails};
use crate::testcase::TestFailure;
use ansi_term::Color::{Blue, Cyan, Green, Red, White};
use std::time::Duration;

// padding to where PASS/FAIL should start
const PAD_TO_START_OF_LINE: &str = "        ";

pub fn print_subtest_header(subtest: &Subtest) {
    let files = cases_in_subdir(subtest.subdir()).len();
    let starting = Green.bold().paint("Starting");
    let name = White.bold().paint(subtest.subdir());

    println!("     {starting} subtest '{name}' with {files} total test cases");
}

pub fn print_summary(total: usize, failed: usize, elapsed: Duration) {
    let switching_color = if failed == 0 { Green } else { Red };

    let passed = Green.paint(format!("{}", total - failed));
    let total = Blue.paint(format!("{total}"));
    let failed = switching_color.paint(format!("{failed}"));
    let summary = switching_color.bold().paint("Summary");
    let time = format!("{:11}s", elapsed.as_secs_f32());

    println!("     {summary} [ {time} ] {total} tests run, {passed} passed, {failed} failed");
}

fn prettify_diff(expected: &str, got: &str) -> String {
    let mut result = String::from("\n");

    for (line, diff) in diff::lines(got, expected).into_iter().enumerate() {
        result += &format!("{:3} |", line + 1);

        let line = match diff {
            diff::Result::Left(l) => Red.paint(format!("- {l}")).to_string(),
            diff::Result::Both(l, _) => format!("  {l}"),
            diff::Result::Right(r) => Green.paint(format!("+ {r}")).to_string(),
        };

        result += &line;
        result += "\n";
    }

    result
}

fn prettify_failure(fail: &TestDetails) -> String {
    match fail.output.as_ref().unwrap_err() {
        TestFailure::CompileError(err) => {
            let prefix = Red.bold().paint("unexpected compilation error:");
            let fixed_err = err.replace('\n', &format!("\n{PAD_TO_START_OF_LINE}"));

            // message, then linebreak and the error
            format!("{prefix}\n{PAD_TO_START_OF_LINE}{fixed_err}")
        }
        TestFailure::Missing { check, full } => {
            let prefix = Red.bold().paint("missing line from CHECK directive:");
            let suffix = Red.bold().paint("output from test:");
            let fixed_output = full.replace('\n', &format!("\n{PAD_TO_START_OF_LINE}"));

            format!("{prefix}\n{PAD_TO_START_OF_LINE}{check}\n\n{suffix}\n{PAD_TO_START_OF_LINE}{fixed_output}")
        }
        TestFailure::Diff { expected, got } => prettify_diff(expected, got),
        TestFailure::Panic(bt, message) => {
            let msg = Red.bold().paint(message);
            let err = Red.paint("runner panicked while running test: ");
            let bt = Red.paint(bt);

            format!("{err}{msg}\n\n{bt}")
        }
        TestFailure::LackOfCompileError => Red
            .bold()
            .paint("expected a compile error but file compiled")
            .to_string(),
    }
}

fn test_results(output: &TestDetails) -> (String, Option<String>) {
    match &output.output {
        Err(_) => {
            let rest = prettify_failure(output);

            (Red.bold().paint("FAIL").to_string(), Some(rest))
        }
        Ok(()) => (Green.bold().paint("pass").to_string(), None),
    }
}

pub fn print_failure(file: String, error: String) {
    println!("{PAD_TO_START_OF_LINE}- - - - - - - - - - - - - - - - - - - - -");
    println!();
    println!(
        "{}{file}{} {error}",
        Red.paint("output from failure of '"),
        Red.paint("':")
    );
}

pub fn print_subtest_result(
    subtest: &Subtest,
    file: &'static str,
    details: TestDetails,
) -> Option<(String, String)> {
    let filename = format!("{}/{}", Cyan.paint(subtest.subdir()), Blue.paint(file));
    let time = format!("{:11}s", details.elapsed.as_secs_f32());
    let (start, rest) = test_results(&details);

    println!("{PAD_TO_START_OF_LINE}{start} [ {time} ] {filename}");

    rest.map(|rest| (filename, rest))
}
