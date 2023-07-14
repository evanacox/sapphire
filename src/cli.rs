//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

//! Contains utility code specifically for the CLI tools located in
//! the `tools/` subdirectory.
//!
//! All of these tools have similar command-line arguments and they all
//! should look/feel uniform, so most of the code is pulled into this
//! module and then used in the drivers of the different tools.

use bpaf::{construct, OptionParser, Parser};
use std::path::PathBuf;
use std::str::FromStr;

const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The format for a tool emitting native code to emit in.
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum MachineFormat {
    /// Human-readable assembly that can be plugged into
    /// a specific assembler
    Asm,
    /// Raw object code that can be plugged into a linker
    Obj,
}

impl FromStr for MachineFormat {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "asm" => MachineFormat::Asm,
            "obj" => MachineFormat::Obj,
            _ => return Err("format must be one of 'asm' or 'obj'"),
        })
    }
}

/// The format for a tool emitting SIR to emit in.
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum IRFormat {
    /// Human-readable IR in a text file.
    IR,
    /// A dense binary format that can be serialized and deserialized
    /// quickly and efficiently, and takes up less space on disk.
    Bitcode,
}

impl FromStr for IRFormat {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "ir" => IRFormat::IR,
            "bc" => IRFormat::Bitcode,
            _ => return Err("format must be one of 'ir' or 'bc'"),
        })
    }
}

/// Basic options that every CLI tool in the suite takes in.
pub struct BaseOptions {
    /// The file to output results to
    pub output: Option<PathBuf>,
    /// Whether or not to run the logging in verbose mode.
    pub verbose: bool,
    /// The list of inputs given to the tool
    pub inputs: Vec<PathBuf>,
}

/// Returns a [`OptionParser`] preconfigured with the standard Sapphire
/// options and additional tool-specific options.
pub fn tool_with<T>(
    description: &'static str,
    usage: &'static str,
    additional: impl Parser<T> + 'static,
) -> OptionParser<(T, BaseOptions)> {
    let res = construct!(additional, default());

    res.to_options()
        .descr(description)
        .version(VERSION)
        .usage(usage)
}

/// Returns a [`OptionParser`] preconfigured with the standard Sapphire
/// options and nothing else.
pub fn tool<T>(description: &'static str, usage: &'static str) -> OptionParser<BaseOptions> {
    default()
        .to_options()
        .descr(description)
        .version(VERSION)
        .usage(usage)
}

/// Gets the baseline default options that every tool needs.
pub fn default() -> impl Parser<BaseOptions> {
    let inputs = inputs();
    let output = output();
    let verbose = verbose();

    construct!(BaseOptions {
        output,
        verbose,
        inputs,
    })
}

/// Gets the output file specified on the CLI, if one exists.
pub fn output() -> impl Parser<Option<PathBuf>> {
    bpaf::long("output")
        .short('o')
        .help("the file to output to")
        .argument::<PathBuf>("FILE")
        .optional()
}

/// Gets the input file specified on the CLI.
pub fn inputs() -> impl Parser<Vec<PathBuf>> {
    bpaf::positional::<PathBuf>("FILES")
        .help("files to read as input to the tool")
        .many()
}

/// Checks for the presence of `-v` or `--verbose`
pub fn verbose() -> impl Parser<bool> {
    bpaf::long("verbose")
        .short('v')
        .help("enable verbose output")
        .flag(true, false)
}

/// An emit argument for tools that emit machine-specific code.
pub fn emit_machine_format() -> impl Parser<MachineFormat> {
    bpaf::long("emit")
        .short('e')
        .help("the machine format to emit, either 'asm' or 'obj'")
        .argument::<MachineFormat>("FORMAT")
        .fallback(MachineFormat::Obj)
}

/// Gets the emit format for a tool that emits SIR
pub fn emit_sir() -> impl Parser<IRFormat> {
    bpaf::long("emit")
        .short('e')
        .help("the SIR format to emit, either 'ir' or 'bc'")
        .argument::<IRFormat>("FORMAT")
        .fallback(IRFormat::Bitcode)
}

/// Option for omitting/leaving the frame pointer
pub enum FramePointer {
    /// Omits the frame pointer in any function where it is possible to do so
    OmitWhenPossible,
    /// Never omits the frame pointer
    NeverOmit,
}

impl FromStr for FramePointer {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "omit" => Ok(FramePointer::OmitWhenPossible),
            "never-omit" => Ok(FramePointer::NeverOmit),
            _ => Err("only options are `omit` or `never-omit`"),
        }
    }
}

/// Whether or not to omit the frame pointer
pub fn frame_pointer() -> impl Parser<Option<FramePointer>> {
    bpaf::long("frame-ptr")
        .help("whether to attempt to omit or never omit the frame pointer")
        .argument::<FramePointer>("OPTION")
        .optional()
}

/// Gets the number of concurrent threads to use for a given task
pub fn jobs() -> impl Parser<Option<usize>> {
    bpaf::long("jobs")
        .short('j')
        .help("the number of concurrent jobs to run tests on")
        .argument::<usize>("JOBS")
        .optional()
}

/// Gets a list of passes to run over the IR
pub fn passes() -> impl Parser<Vec<String>> {
    bpaf::long("passes")
        .short('p')
        .help("a pass to run over the input")
        .argument::<String>("PASS-NAME")
        .many()
}
