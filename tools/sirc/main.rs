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
    let matches = cli::tool("sirc", "Sapphire IR Static Compiler").get_matches();

    for file in cli::inputs(&matches) {
        let source = fs::read_to_string(&file).expect("file did not exist");

        match reader::parse_sir(&file, &source) {
            Ok(module) => {
                analysis::print_module(&module);
            }
            Err(e) => {
                eprintln!("failed to parse: {e}");
            }
        }
    }
}
