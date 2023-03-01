//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::display;
use crate::runners::*;
use crate::subtest::Subtest;
use std::io;
use std::time::Duration;
use threadpool::ThreadPool;

const SUBTESTS: [Subtest; 7] = [
    parse_subtest(),
    domtree_subtest(),
    dce_subtest(),
    mem2reg_subtest(),
    gvn_subtest(),
    simplifyinst_subtest(),
    split_crit_edges_subtest(),
];

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
        display::print_subtest_header(test);

        for (file, result) in test.run(pool) {
            total += 1;
            total_time += result.elapsed;

            if let Some(rest) = display::print_subtest_result(test, file, result) {
                failed.push(rest);
            }
        }
    }

    display::print_summary(total, failed.len(), total_time);

    match failed.len() {
        0 => Ok(()),
        _ => {
            for (file, rest) in failed {
                display::print_failure(file, rest);
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
        "domtree" => run_tests(&SUBTESTS[1..2], &mut pool),
        "dce" => run_tests(&SUBTESTS[2..3], &mut pool),
        "mem2reg" => run_tests(&SUBTESTS[3..4], &mut pool),
        "gvn" => run_tests(&SUBTESTS[4..5], &mut pool),
        "simplifyinst" => run_tests(&SUBTESTS[5..6], &mut pool),
        "splitcritedges" => run_tests(&SUBTESTS[6..7], &mut pool),
        _ => unreachable!(),
    }
}
