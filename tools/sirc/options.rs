//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use bpaf::Parser;
use sapphire::cli::{emit_machine_format, frame_pointer, verify, FramePointer, MachineFormat};
use sapphire::codegen::x86_64::{X86_64Assembly, X86_64ObjectFile};
use sapphire::codegen::{CodegenOptions, TargetPair};
use sapphire::{cli, cli::BaseOptions};
use std::str::FromStr;
use std::sync::OnceLock;

/// The options given by the user, both inferred and explicit.
pub struct Options {
    /// Options to pass into the backend
    pub codegen: CodegenOptions,
    /// The register allocator to use
    pub reg_alloc: RegAlloc,
    /// The base Sapphire tool options
    pub base: BaseOptions,
    /// The target being generated for
    pub target: TargetPair,
    /// The format being generated
    pub format: MachineFormat,
    /// The level of optimization to perform
    pub opt: OptLevel,
    /// Whether or not to verify the IR
    pub verify: bool,
    /// Whether to print the output to stdout
    pub print: bool,
    /// Whether to emit fixed interval comments
    pub fixed_intervals: bool,
    /// If we're targeting an x86-64 platform and emitting assembly,
    /// this is the format to emit.
    pub x86_64_asm: Option<X86_64Assembly>,
    /// If we're targeting an x86-64 platform and emitting object code,
    /// this is the format to emit.
    pub x86_64_obj: Option<X86_64ObjectFile>,
}

static DESCRIPTION: OnceLock<String> = OnceLock::new();

/// Parses and infers all options necessary for the compiler.
///
/// Some options are automatically inferred from the environment if they
/// aren't explicit (e.g. target platform/format).
pub fn parse_options() -> Options {
    let default = default_target();

    let (
        (format, omit_fp, x86_asm, x86_obj, target, regalloc, opt, verify, print, fixed_intervals),
        base,
    ) = cli::tool_with(
        &DESCRIPTION.get_or_init(|| {
            format!(
                "static compiler for Sapphire IR (default target: {})",
                default_target()
            )
        }),
        "Usage: sirc [options] <input ir>",
        bpaf::construct!(
            emit_machine_format(),
            frame_pointer(),
            x86_64_asm_format(),
            x86_64_object_format(),
            target_pair(),
            reg_alloc(),
            opt_level(),
            verify(),
            print(),
            fixed_intervals()
        ),
    )
    .run();

    // first: do we have a target?
    let target = target.unwrap_or(default);
    let reg_alloc = match regalloc {
        Some(r) => r,
        None => match opt {
            OptLevel::Debug => RegAlloc::Linear,
            OptLevel::Release => RegAlloc::Graph,
        },
    };

    let omit_fp = match omit_fp {
        Some(FramePointer::OmitWhenPossible) => true,
        Some(FramePointer::NeverOmit) => false,
        None => match opt {
            OptLevel::Debug => false,
            OptLevel::Release => true,
        },
    };

    Options {
        codegen: CodegenOptions {
            omit_frame_pointer: omit_fp,
        },
        reg_alloc,
        base,
        target,
        format,
        opt,
        verify,
        print,
        fixed_intervals,
        x86_64_asm: x86_asm,
        x86_64_obj: x86_obj,
    }
}

#[cfg(target_family = "windows")]
fn default_target() -> TargetPair {
    use windows_sys::Win32::System::SystemInformation::{
        IMAGE_FILE_MACHINE_AMD64, IMAGE_FILE_MACHINE_ARM64, IMAGE_FILE_MACHINE_UNKNOWN,
    };
    use windows_sys::Win32::System::Threading::{GetCurrentProcess, IsWow64Process2};

    // see https://learn.microsoft.com/en-us/windows/win32/api/wow64apiset/nf-wow64apiset-iswow64process2
    //
    // if we're running under "WOW64" (x64 emulator) we may get fake information from GetSystemInfo and
    // GetNativeSystemInfo, so we use this instead
    unsafe {
        let handle = GetCurrentProcess();
        let mut process_machine = IMAGE_FILE_MACHINE_UNKNOWN;
        let mut host_machine = IMAGE_FILE_MACHINE_UNKNOWN;
        let result = IsWow64Process2(handle, &mut process_machine, &mut host_machine);

        // if it's zero we fail, fix this later
        assert_ne!(
            result, 0,
            "unknown error while detecting target, please use `--target=` explicitly"
        );

        match host_machine {
            IMAGE_FILE_MACHINE_ARM64 => TargetPair::Arm64Windows,
            IMAGE_FILE_MACHINE_AMD64 => TargetPair::X86_64Windows,
            _ => panic!("unknown host config, please use `--target=` explicitly"),
        }
    }
}

#[cfg(target_family = "unix")]
fn default_target() -> TargetPair {
    use std::ffi::CStr;
    use std::mem::MaybeUninit;

    let uname = unsafe {
        let mut data = MaybeUninit::uninit();
        let result = libc::uname(data.as_mut_ptr());

        assert_eq!(
            result, 0,
            "unknown host config, please use `--target=` explicitly"
        );

        // libc::uname initialized the data
        data.assume_init()
    };

    let (arch, os) = unsafe {
        // this is guaranteed to be populated by `libc::uname`,
        // POSIX guarantees a null terminator
        (
            CStr::from_ptr(uname.machine.as_ptr()),
            CStr::from_ptr(uname.sysname.as_ptr()),
        )
    };

    let arch_str = arch.to_str().expect("machine string is not utf-8");
    let os_str = os.to_str().expect("os string is not utf-8");

    match (arch_str, os_str) {
        ("arm64", "Darwin") => TargetPair::Arm64macOS,
        ("x86_64", "Darwin") => TargetPair::X86_64macOS,
        ("aarch64", i) if i.contains("linux") || i.contains("Linux") => TargetPair::Aarch64Linux,
        ("x86_64", i) if i.contains("linux") || i.contains("Linux") => TargetPair::X86_64Linux,
        _ => panic!("unknown `uname` hardware configuration, use `--target` explicitly. got arch = `{arch_str}`, os = `{os_str}`"),
    }
}

fn target_pair() -> impl Parser<Option<TargetPair>> {
    bpaf::long("target")
        .help("the target to generate code for (affects default emit format)")
        .argument::<TargetPair>("TARGET")
        .optional()
}

fn fixed_intervals() -> impl Parser<bool> {
    bpaf::long("fixed-intervals")
        .help("whether to attempt to print fixed-interval information")
        .flag(true, false)
}

/// Which register allocator to use
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum RegAlloc {
    /// The naive stack allocator (spills every value on def and reloads on every use)
    Stack,
    /// A linear-scan allocator, slower than [`Self::Stack`] at compile time but
    /// generates code that performs significantly better.
    Linear,
    /// A graph-coloring allocator, much slower than [`Self::Linear`] but generates
    /// the best code out of the three.
    Graph,
    /// Only used for debug reasons, does not perform register allocation
    None,
}

impl FromStr for RegAlloc {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "stack" => Ok(RegAlloc::Stack),
            "linear" => Ok(RegAlloc::Linear),
            "graph" => Ok(RegAlloc::Graph),
            "none" => Ok(RegAlloc::None),
            _ => Err("the only available allocators are `stack`, `linear`, and `graph`"),
        }
    }
}

fn reg_alloc() -> impl Parser<Option<RegAlloc>> {
    bpaf::long("regalloc")
        .help("which register allocator to use (default dependent on opt level)")
        .argument::<RegAlloc>("ALLOC")
        .optional()
}

/// The optimization levels that the compiler supports.
///
/// This is currently very coarse-grained, either "generate naive code
/// quickly" or "generate decent code slowly."
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum OptLevel {
    /// Almost all optimizations disabled, codegen is fairly quick
    Debug,
    /// Optimizations enabled, codegen is slower
    Release,
}

fn opt_level() -> impl Parser<OptLevel> {
    bpaf::long("optimize")
        .short('O')
        .help("whether to enable optimizations")
        .flag(OptLevel::Release, OptLevel::Debug)
}

fn x86_64_asm_format() -> impl Parser<Option<X86_64Assembly>> {
    bpaf::long("x86-64-asm-format")
        .help("the specific dialect of x86-64 assembly to generate")
        .argument::<X86_64Assembly>("FORMAT")
        .optional()
}

fn x86_64_object_format() -> impl Parser<Option<X86_64ObjectFile>> {
    bpaf::long("x86-64-obj-format")
        .help("the specific type of file to generate for x86-64 binaries")
        .argument::<X86_64ObjectFile>("FORMAT")
        .optional()
}

fn print() -> impl Parser<bool> {
    bpaf::long("print")
        .help("whether to print the result for every file onto stdout")
        .flag(true, false)
}
