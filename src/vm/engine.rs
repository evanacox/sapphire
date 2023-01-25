//======---------------------------------------------------------------======//
//                                                                           //
// Copyright 2022-2023 Evan Cox <evanacox00@gmail.com>. All rights reserved. //
//                                                                           //
// Use of this source code is governed by a BSD-style license that can be    //
// found in the LICENSE.txt file at the root of this project, or at the      //
// following link: https://opensource.org/licenses/BSD-3-Clause              //
//                                                                           //
//======---------------------------------------------------------------======//

use crate::ir::Module;
use std::any::Any;

/// Provides a translation layer between the specific values
/// that a given engine implementation understands internally and the outside world.
///
/// This is meant to allow foreign values to be passed in as arguments/returned from
/// calls to functions and whatnot.
pub enum GenericForeignValue {
    /// A `bool` value
    Bool(bool),
    /// An `i8` value
    Int8(u8),
    /// An `i16` value
    Int16(u16),
    /// An `i32` value
    Int32(u32),
    /// An `i64` value
    Int64(u64),
    /// An `f32` value
    Float32(f32),
    /// An `f64` value
    Float64(f64),
    /// An array of SIR values
    Array(Box<[GenericForeignValue]>),
    /// A structure of SIR values
    Struct(Box<[GenericForeignValue]>),
}

/// Abstract interface for an "engine" that can execute SIR.
///
/// How the engine decides to do that is completely irrelevant, this interface
/// only exposes the basic operations that are necessary for a user of that
/// engine to actually do meaningful work with it.  
pub trait Engine {
    /// Creates an engine instance that will execute `module`.
    fn with_module(module: Module) -> Self;

    /// Registers a function with a given name as the definition for
    /// a function *only declared* in the SIR.
    ///
    /// # Safety
    /// This function **must** match the signature of the associated declaration
    /// in the SIR, this condition cannot be checked but if it is not true, the interpreter
    /// will end up calling this function with invalid arguments (and the behavior
    /// of the program will become undefined).
    unsafe fn register_external_function<T: Any>(name: &str, func: extern "C" fn() -> T);

    /// Runs the entry point specified by `entry`. The value returned
    /// by that function (if it isn't `void`) is returned.
    ///
    /// # Safety
    /// If the SIR being executed has undefined behavior, the behavior of this
    /// call is undefined. Implementations should attempt to detect UB and abort where
    /// doing does not have a significant impact on performance, but obviously that is
    /// not possible in the general case.
    unsafe fn run(entry: &str) -> Option<GenericForeignValue>;

    /// Runs the module as-if it was a C program, and returns the result.
    ///
    /// This will operate as-if the C runtime is correctly initialized as needed,
    /// and the entry point is assumed to be `int main(int, char**)`.
    ///
    /// # Safety
    /// See the 'Safety' section on [`Self::run`].
    unsafe fn run_c(args: &[&str]) -> i32;
}
