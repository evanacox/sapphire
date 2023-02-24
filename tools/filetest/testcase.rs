//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::subtest::TestResult;

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum TestFailure {
    Diff { expected: String, got: String },
    Missing { check: String, full: String },
    CompileError(String),
    Panic(String, String),
    LackOfCompileError,
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub enum Check<'data> {
    // rest
    MatchEntireFile(&'data str),
    // expected
    MatchSection(String),
    // checks
    IndividualChecks(Vec<&'data str>),
    // error message
    CompileError(String),
}

fn first_line(contents: &str) -> Option<(&str, &str)> {
    contents
        .find('\n')
        .map(|idx| (&contents[0..idx], &contents[idx + 1..]))
}

fn find_match_section<'data>(rest: &str) -> Check<'data> {
    let mut lines = rest.lines();
    let mut section = String::default();

    assert_eq!(lines.next(), Some(";"));

    for line in lines
        // we don't do `trim_start_matches(';')` because an empty line `;` needs to be empty
        // but we also need to maintain whitespace, so we can't just do .trim_start with one space
        .map(|line| line.trim_start_matches("; ").trim_end())
        .take_while(|line| *line != ";;")
    {
        if line != ";" {
            section.push_str(line);
        }

        section.push('\n');
    }

    Check::MatchSection(section)
}

fn find_individual_checks(rest: &str) -> Check<'_> {
    let lines = rest.lines();
    let mut checks = Vec::default();

    for line in lines
        .map(|line| line.trim_start())
        .filter(|line| line.starts_with("; CHECK: "))
    {
        let check = line.trim_start_matches("; CHECK: ");

        checks.push(check);
    }

    Check::IndividualChecks(checks)
}

fn find_checks<'data>(name: &str, contents: &'data str) -> Check<'data> {
    let (first, rest) = match first_line(contents) {
        Some(data) => data,
        None => return Check::IndividualChecks(Vec::default()),
    };

    if first.starts_with("; MATCH-ENTIRE") {
        return Check::MatchEntireFile(rest);
    }

    if first.starts_with("; MATCH-SECTION") {
        return find_match_section(rest);
    }

    if first.starts_with("; COMPILE-ERROR: ") {
        return Check::CompileError(first.trim_start_matches("; COMPILE-ERROR: ").to_string());
    }

    if first.starts_with("; STANDARD") {
        return find_individual_checks(rest);
    }

    panic!("test '{name}' did not provide `; <TYPE>` header for `filetest`. got: '{first}'")
}

fn match_entire_file(output: TestResult, expected: &str) -> Result<(), TestFailure> {
    match output {
        TestResult::Output(data) if data == expected => Ok(()),
        TestResult::CompileError(err) => Err(TestFailure::CompileError(err)),
        TestResult::Output(data) => Err(TestFailure::Diff {
            expected: expected.to_string(),
            got: data,
        }),
    }
}

fn match_compile_error(output: TestResult, err: &str) -> Result<(), TestFailure> {
    match output {
        TestResult::CompileError(got) if got.contains(err) => Ok(()),
        TestResult::CompileError(got) => Err(TestFailure::CompileError(got)),
        _ => Err(TestFailure::LackOfCompileError),
    }
}

fn match_section(output: TestResult, section: &str) -> Result<(), TestFailure> {
    match output {
        TestResult::Output(data) if data.contains(section) => Ok(()),
        TestResult::CompileError(err) => Err(TestFailure::CompileError(err)),
        TestResult::Output(data) => Err(TestFailure::Diff {
            expected: section.to_string(),
            got: data,
        }),
    }
}

fn match_checks(output: TestResult, checks: &[&str]) -> Result<(), TestFailure> {
    let data = match output {
        TestResult::Output(data) => data,
        TestResult::CompileError(err) => return Err(TestFailure::CompileError(err)),
    };

    let mut checks = checks.iter().peekable();

    for line in data.lines() {
        let check = match checks.peek() {
            Some(check) => **check,
            None => break,
        };

        if line == check {
            let _ = checks.next();
        }
    }

    match checks.next() {
        None => Ok(()),
        Some(check) => Err(TestFailure::Missing {
            check: check.to_string(),
            full: data,
        }),
    }
}

#[derive(Debug, Hash, Eq, PartialEq)]
pub struct FileTestCase<'data> {
    check: Check<'data>,
}

impl<'data> FileTestCase<'data> {
    pub fn from_raw(name: &str, raw: &'data str) -> Self {
        Self {
            check: find_checks(name, raw),
        }
    }

    pub fn check(&self, output: TestResult) -> Result<(), TestFailure> {
        match &self.check {
            Check::MatchEntireFile(expected) => match_entire_file(output, expected),
            Check::MatchSection(section) => match_section(output, section),
            Check::CompileError(error) => match_compile_error(output, error),
            Check::IndividualChecks(checks) => match_checks(output, checks),
        }
    }
}
