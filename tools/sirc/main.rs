//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use sapphire::analysis;
use sapphire::cli;
use sapphire::reader;
use std::fs;

fn main() {
    let (_, base) = cli::tool(
        "static compiler for Sapphire IR",
        "Usage: sirc [options] <input ir> ",
        cli::emit_machine_format(),
    )
    .run();

    // for now, non-utf8 path names aren't real
    let source = fs::read_to_string(&base.input).expect("file did not exist");
    let filename = base.input.into_os_string().into_string().unwrap();

    match reader::parse_sir(&filename, &source) {
        Ok(module) => {
            analysis::print_module(&module);
        }
        Err(e) => {
            eprintln!("failed to parse: {e}");
        }
    }
}
