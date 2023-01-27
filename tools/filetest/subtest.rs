//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::discovery;
use crate::testcase::TestFailure;
use backtrace::Backtrace;
use std::cell::RefCell;
use std::sync::mpsc;
use std::sync::mpsc::Receiver;
use std::time::{Duration, SystemTime};
use threadpool::ThreadPool;

thread_local! {
    pub static BACKTRACE: RefCell<Option<Backtrace>> = RefCell::new(None);
}

pub enum TestResult {
    Output(String),
    CompileError(String),
}

pub struct TestDetails {
    pub elapsed: Duration,
    pub output: Result<(), TestFailure>,
}

pub struct Subtest {
    subdir: &'static str,
    runner: fn(&str, &str) -> TestResult,
}

impl Subtest {
    pub const fn new(subdir: &'static str, runner: fn(&str, &str) -> TestResult) -> Self {
        Self { subdir, runner }
    }

    pub fn subdir(&self) -> &'static str {
        self.subdir
    }

    pub fn run(&self, pool: &mut ThreadPool) -> Receiver<(&'static str, TestDetails)> {
        let (send, recv) = mpsc::channel();

        for (name, contents, case) in discovery::cases_in_subdir(self.subdir) {
            let send = send.clone();
            let runner = self.runner;

            pool.execute(move || {
                let start = SystemTime::now();
                let result = std::panic::catch_unwind(|| runner(name, contents));
                let end = SystemTime::now();
                let output = match result {
                    Ok(output) => case.check(output),
                    Err(_) => {
                        let b = BACKTRACE.with(|b| b.borrow_mut().take()).unwrap();

                        Err(TestFailure::Panic(format!("{b:#?}")))
                    }
                };

                // we want to display the time taken on a per-test basis
                let details = TestDetails {
                    elapsed: end.duration_since(start).unwrap(),
                    output,
                };

                send.send((name.as_str(), details)).expect("unable to send")
            });
        }

        recv
    }
}
