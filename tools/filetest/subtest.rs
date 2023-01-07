//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::discovery;
use std::sync::mpsc;
use std::sync::mpsc::Receiver;
use std::time::{Duration, SystemTime};
use threadpool::ThreadPool;

pub enum TestFailure {
    Diff { expected: String, got: String },
    CompileError(String),
    LackOfCompileError,
}

pub struct TestDetails {
    pub elapsed: Duration,
    pub failure: Option<Box<TestFailure>>,
}

pub struct Subtest {
    subdir: &'static str,
    runner: fn(&str, &str) -> Option<TestFailure>,
}

impl Subtest {
    pub const fn new(subdir: &'static str, runner: fn(&str, &str) -> Option<TestFailure>) -> Self {
        Self { subdir, runner }
    }

    pub fn subdir(&self) -> &'static str {
        self.subdir
    }

    pub fn run(&self, pool: &mut ThreadPool) -> Receiver<(&'static str, TestDetails)> {
        let (send, recv) = mpsc::channel();

        for (name, contents) in discovery::cases_in_subdir(self.subdir) {
            let send = send.clone();
            let runner = self.runner;

            pool.execute(move || {
                let start = SystemTime::now();
                let result = runner(name, contents);
                let end = SystemTime::now();

                // we want to display the time taken on a per-test basis
                let details = TestDetails {
                    elapsed: end.duration_since(start).unwrap(),
                    failure: result.map(|failure| Box::new(failure)),
                };

                send.send((name.as_str(), details)).expect("unable to send")
            });
        }

        recv
    }
}
