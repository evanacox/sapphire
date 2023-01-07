//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::discovery::cases_in_subdir;
use crate::parse::parse_subtest;
use crate::subtest::{Subtest, TestDetails, TestFailure};
use ansi_term::Color::{Blue, Cyan, Green, Red, White};
use std::io;
use std::time::Duration;
use threadpool::ThreadPool;

const SUBTESTS: [Subtest; 1] = [parse_subtest()];

// padding to where PASS/FAIL should start
const PAD_TO_START_OF_LINE: &str = "        ";

fn pool_for_jobs(jobs: Option<usize>) -> ThreadPool {
    match jobs {
        Some(n) => ThreadPool::new(n),
        None => ThreadPool::default(),
    }
}

fn run_tests(tests: &[Subtest], pool: &mut ThreadPool) -> io::Result<()> {
    let mut total = 0usize;
    let mut total_time = Duration::default();
    let mut failed = Vec::default();

    for test in tests {
        print_subtest_header(test);

        for (file, result) in test.run(pool) {
            total += 1;
            total_time += result.elapsed;

            if let Some(rest) = print_subtest_result(test, file, result) {
                failed.push(rest);
            }
        }
    }

    print_summary(total, failed.len(), total_time);

    match failed.len() {
        0 => Ok(()),
        _ => {
            for (file, rest) in failed {
                print_failure(file, rest);
            }

            Err(io::Error::from(io::ErrorKind::InvalidInput))
        }
    }
}

pub fn run_all(jobs: Option<usize>) -> io::Result<()> {
    let mut pool = pool_for_jobs(jobs);

    run_tests(&SUBTESTS, &mut pool)
}

pub fn run_subtest(name: &str, jobs: Option<usize>) -> io::Result<()> {
    let mut pool = pool_for_jobs(jobs);

    match name {
        "parse" => run_tests(&SUBTESTS[0..1], &mut pool),
        _ => unreachable!(),
    }
}

fn print_subtest_header(subtest: &Subtest) {
    let files = cases_in_subdir(subtest.subdir()).len();
    let starting = Green.bold().paint("Starting");
    let name = White.bold().paint(subtest.subdir());

    println!("     {starting} subtest '{name}' with {files} total test cases");
}

fn print_summary(total: usize, failed: usize, elapsed: Duration) {
    let switching_color = if failed == 0 { Green } else { Red };

    let passed = Green.paint(format!("{}", total - failed));
    let total = Blue.paint(format!("{total}"));
    let failed = switching_color.paint(format!("{}", failed));
    let summary = switching_color.bold().paint("Summary");
    let time = format!("{:11}s", elapsed.as_secs_f32());

    println!("     {summary} [ {time} ] {total} tests run, {passed} passed, {failed} failed");
}

fn prettify_diff(expected: &str, got: &str) -> String {
    let mut result = String::from("\n");

    for (line, diff) in diff::lines(got, expected).into_iter().enumerate() {
        result += &format!("{:3} |", line + 1);

        let line = match diff {
            diff::Result::Left(l) => Red.paint(format!("-{l}")).to_string(),
            diff::Result::Both(l, _) => format!(" {l}"),
            diff::Result::Right(r) => Green.paint(format!("+{r}")).to_string(),
        };

        result += &line;
        result += "\n";
    }

    result
}

fn prettify_failure(fail: &TestFailure) -> String {
    match fail {
        TestFailure::CompileError(err) => {
            let prefix = Red.bold().paint("compiler emitted error, see below:");
            let fixed_err = err.replace('\n', &format!("\n{PAD_TO_START_OF_LINE}"));

            // message, then linebreak and the error
            format!("{prefix}\n{PAD_TO_START_OF_LINE}{fixed_err}")
        }
        TestFailure::Diff { expected, got } => prettify_diff(expected, got),
        TestFailure::LackOfCompileError => Red
            .bold()
            .paint("expected a compile error but file compiled")
            .to_string(),
    }
}

fn test_results(failure: Option<Box<TestFailure>>) -> (String, Option<String>) {
    match failure {
        Some(fail) => {
            let rest = prettify_failure(fail.as_ref());

            (Red.bold().paint("FAIL").to_string(), Some(rest))
        }
        None => (Green.bold().paint("pass").to_string(), None),
    }
}

fn print_failure(file: String, error: String) {
    println!("{PAD_TO_START_OF_LINE}- - - - - - - - - - - - - - - - - - - - -");
    println!();
    println!(
        "{}{file}{} {error}",
        Red.paint("output from failure of '"),
        Red.paint("':")
    );
}

fn print_subtest_result(
    subtest: &Subtest,
    file: &'static str,
    details: TestDetails,
) -> Option<(String, String)> {
    let filename = format!("{}/{}", Cyan.paint(subtest.subdir()), Blue.paint(file));
    let time = format!("{:11}s", details.elapsed.as_secs_f32());
    let (start, rest) = test_results(details.failure);

    println!("{PAD_TO_START_OF_LINE}{start} [ {time} ] {filename}");

    rest.map(|rest| (filename, rest))
}
