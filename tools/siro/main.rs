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
use sapphire::cli::{passes, verify, BaseOptions};
use std::io::ErrorKind;
use std::{fs, io};

fn main() -> io::Result<()> {
    let (base, verify, passes) = parse_options();

    assert_eq!(base.inputs.len(), 1, "can only optimize one file at a time");

    let input = base.inputs.last().unwrap();
    let source = fs::read_to_string(input).expect("file did not exist");

    if let Err(()) = optimize_single_file(&source, &base, verify, &passes) {
        return Err(io::Error::new(
            ErrorKind::InvalidInput,
            "failed to optimize file",
        ));
    }

    Ok(())
}

fn parse_options() -> (BaseOptions, bool, Vec<String>) {
    let ((passes, verify), base) = cli::tool_with(
        "sapphire .sir -> .sir optimizer and analysis printer",
        "Usage: siro [options] <input ir>",
        bpaf::construct!(passes(), verify()),
    )
    .run();

    (base, verify, passes)
}

fn optimize_single_file(
    source: &str,
    base: &BaseOptions,
    verify: bool,
    passes: &[String],
) -> Result<(), ()> {
    match sapphire::parse_sir("<siro>", source) {
        Ok(mut module) => {
            sapphire::run_passes(&mut module, verify, passes, &[]);

            match &base.output {
                Some(path) => {
                    let ir = sapphire::analysis::stringify_module(&module);

                    let err = format!("unable to write output to file `{}`", path.display());

                    fs::write(path, ir).expect(&err)
                }
                None => {
                    sapphire::analysis::print_module(&module);
                }
            }

            Ok(())
        }
        Err(e) => {
            eprintln!("failed to parse: {e}");

            Err(())
        }
    }
}
