# `filetest`: File-driven Test Runner

This is a very similar (albeit extremely cut-down) tool to `FileCheck` from LLVM. It's a simple, fast way of writing
data-driven regression tests for the compiler. 

## Tests and Runners

Tests are defined in terms of "subtests" and "cases" for those subtests. Subtests are subsets of
the complete list of test cases that are run through a specific "runner" that is built into 
`filetest`. These runners are written in the `runners/` subdirectory of `filetest/`, and are
enabled in `runner.rs`.

> Note: The reason it is built this way is to allow better access to compiler APIs in regression tests,
> as writing the runners in Rust gives full access to both the Sapphire API and the Rust language.
> 
> This tool may end up changing to more of a command-based model where tests are defined in terms of commands
> to execute that output data to be matched on, but as of right now runners are hard-coded. 

Runners operate on a subset of the total list of test cases, each subdirectory in the `tests/` directory
is considered to correspond to a subtest. `tests/parse/` => `parse` subtest, `tests/domtree/` => `domtree`
subtest, etc. These are automatically discovered when `filetest` is executed. 

## Format

`filetest` works with the idea of "checks," and it provides several types of checks
that can be useful in different circumstances.

All `filetest` test cases (files) must start with a header of the following format:

```llvm
; <CHECK TYPE>
```

where `<CHECK TYPE>` is one of the following:

- `STANDARD`: Normal `CHECK` directive style, the output should contain the content of each CHECK line
- `MATCH-ENTIRE`: The output of a given test should exactly match the rest of the file (starting at the beginning of the next line)
- `MATCH-SECTION`: The output should contain a given output

Note that the entire file is still given as input for the test, comments are not stripped out. This
should not matter for your test. 

## Check Types

### `STANDARD`

This is very similar to `CHECK` directives in LLVM's `FileCheck`. Any line that (after whitespace
is trimmed from the beginning) follows the following format is considered to be a `CHECK` directive:

```llvm
; CHECK: <check content>
```

Each of these checks must appear **in order** in the output of the test, although they may
have other lines inserted between them. Consider the following tests:

| Test Case                                               | Output                                    |
|---------------------------------------------------------|-------------------------------------------|
| ```llvm<br/>; STANDARD<br/>; CHECK: a<br/>; CHECK: b``` | ``` whatever<br/>a<br/>whatever<br/>b ``` |

This would be considered to pass the test. While `a` and `b` are not one-after-the-other in the test's output,
they are in the correct order relative to one another, and they are both present. 

| Test Case                                               | Output                                    |
|---------------------------------------------------------|-------------------------------------------|
| ```llvm<br/>; STANDARD<br/>; CHECK: a<br/>; CHECK: b``` | ``` whatever<br/>b<br/>whatever<br/>a ``` |

This would be considered to not pass the test. While `a` and `b` are both present in the output, they
are not in the correct relative order.

If it is necessary to not have anything between checks, use `MATCH-SECTION`.

### `MATCH-ENTIRE`

This directive is simple. It takes everything in the file after the `; MATCH-ENTIRE` directive
and expects the output to match this exactly. This is really only used for the parser regression tests
where the parser/writer should output the same thing that was input. 

```llvm
; MATCH-ENTIRE
fn i32 @main(i32, ptr) {
entry(i32 %argc, ptr %argv):
  %0 = iconst i32 0
  ret i32 %0
}
```

### `MATCH-SECTION`

This directive allows defining an exact textual structure that should appear somewhere in the output. After
the `MATCH-SECTION` directive, an `;;` line denotes the end of the section to look for in the output, and
the first line after is expected to be an empty `;` line.

> Note: While a bit odd, this makes it easier to read the test cases and allows blank lines to be
> part of the tests.

```llvm
; MATCH-SECTION
;
; fn void @test() {
; entry:
;   ret void
; }
;;
fn void @test() {
entry:
  ret void
}
```