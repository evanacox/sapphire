//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022 Evan Cox <evanacox00@gmail.com>. All rights reserved.      //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Contains lots of utility code specifically for the CLI tools located in
//! the `tools/` subdirectory of the repository. All of these tools have
//! similar command-line arguments and they all should look/feel uniform, so
//! most of the code is pulled into this module and then used in the drivers
//! of the different tools.

use clap::{Arg, ArgAction, ArgMatches, Command};

const VERSION: &str = env!("CARGO_PKG_VERSION");

const AUTHOR: &str = env!("CARGO_PKG_AUTHORS");

/// Returns a [`clap::Command`] preconfigured with the standard Sapphire
/// options, version, etc.
///
/// Helps make everything a bit more standardized in the CLI tools.
pub fn tool(name: &'static str, description: &'static str) -> Command {
    Command::new(name)
        .version(VERSION)
        .author(AUTHOR)
        .about(description)
        .arg(Arg::new("output").long("output").short('o'))
        .arg(Arg::new("input").action(ArgAction::Append))
}

/// Gets the output file specified on the CLI, if one exists.
pub fn output(matches: &ArgMatches) -> Option<&str> {
    matches.get_one::<String>("output").map(|s| s.as_str())
}

/// Gets the input files specified on the CLI.
pub fn inputs(matches: &ArgMatches) -> Vec<String> {
    match matches.get_many::<String>("input") {
        Some(refs) => refs.cloned().collect(),
        None => Vec::default(),
    }
}
