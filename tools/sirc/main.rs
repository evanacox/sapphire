//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use sapphire::cli;
use std::fs;

fn main() {
    let (_, base) = cli::tool_with(
        "static compiler for Sapphire IR",
        "Usage: sirc [options] <input ir>",
        cli::emit_machine_format(),
    )
    .run();

    for input in base.inputs {
        // for now, non-utf8 path names aren't real
        let source = fs::read_to_string(&input).expect("file did not exist");
        let filename = input.into_os_string().into_string().unwrap();

        match sapphire::parse_sir(&filename, &source) {
            Ok(module) => {
                dbg!(module);
            }
            Err(e) => {
                eprintln!("failed to parse: {e}");
            }
        }
    }
}
