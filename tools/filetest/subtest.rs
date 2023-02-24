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
use std::cell::RefCell;
use std::panic;
use std::panic::PanicInfo;
use std::sync::mpsc;
use std::sync::mpsc::Receiver;
use std::time::{Duration, SystemTime};
use threadpool::ThreadPool;

thread_local! {
    static FAILURE: RefCell<Option<(String, String)>> = RefCell::new(None);
}

pub fn panic_hook(payload: &PanicInfo<'_>) {
    let message = match payload.payload().downcast_ref::<&'static str>() {
        Some(msg) => *msg,
        None => match payload.payload().downcast_ref::<String>() {
            Some(msg) => msg.as_str(),
            None => "no panic message",
        },
    };

    let mut count = 0usize;
    let mut backtrace = String::default();
    let cwd_string = format!(
        "{:?}",
        std::fs::canonicalize(std::env::current_dir().unwrap()).unwrap()
    );

    let cwd = cwd_string.trim_start_matches('"').trim_end_matches('"');

    backtrace::trace(|frame| {
        backtrace::resolve_frame(frame, |symbol| {
            //
            // this mess is for extracting the part of the callstack that we care about,
            // the part involving `sapphire` or `filetest` code. the rest of it is fluff
            //
            if let Some(name) = symbol.name() {
                let symbol_name = name.as_str().unwrap();

                if symbol_name.contains("sapphire") || symbol_name.contains("filetest") {
                    backtrace += &format!("  {count}: {name:#}\n");
                    count += 1;

                    if let Some(filename) = symbol.filename() {
                        let as_str = format!("{filename:?}");
                        let relative = as_str
                            .trim_start_matches('"')
                            .trim_end_matches('"')
                            .trim_start_matches(cwd);

                        // lineno may not always exist, same with colno
                        let lineno = match (symbol.lineno(), symbol.colno()) {
                            (Some(line), Some(col)) => format!(":{line}:{col}"),
                            (Some(line), _) => format!(":{line}"),
                            _ => String::new(),
                        };

                        backtrace += &format!("             at {relative}{lineno}\n");
                    }
                }
            }
        });

        true // keep going to the next frame
    });

    FAILURE.with(|failure| *failure.borrow_mut() = Some((backtrace, message.to_string())));
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
                let output = panic::catch_unwind(|| runner(name, contents));
                let end = SystemTime::now();

                let result = match output {
                    Ok(out) => case.check(out),
                    Err(_) => {
                        let (bt, message) = FAILURE.with(|failure| failure.take().unwrap());

                        Err(TestFailure::Panic(bt, message))
                    }
                };

                // we want to display the time taken on a per-test basis
                let details = TestDetails {
                    elapsed: end.duration_since(start).unwrap(),
                    output: result,
                };

                send.send((name.as_str(), details)).expect("unable to send")
            });
        }

        recv
    }
}
