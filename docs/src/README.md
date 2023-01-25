# Preface

Sapphire is a toy compiler framework, heavily inspired by both [LLVM](https://www.llvm.org) and the
Cranelift compiler in [Wasmtime](https://wasmtime.dev/). 

Both of those are much better projects to look at for modern optimizing compilers than this is, you
can find the actual source code at the following:

- [LLVM](https://github.com/llvm/llvm-project/tree/main/llvm), in the `llvm/` subdir of the LLVM monorepo
- [Cranelift](https://github.com/bytecodealliance/wasmtime/tree/main/cranelift), in the `cranelift/` subdir of Wasmtime

## API Documentation

This book does not contain any API documentation for the Sapphire library. If you want that,
you need to go [here](https://pages.evanacox.io/sapphire/api/sapphire).

## SIR

SIR is the intermediary language that everything[^1] inside of Sapphire speaks in. All optimizing transformations
are SIR -> SIR, all analyses work on SIR, etc. SIR is your standard SSA-based IR with memory operations, the only
remotely interesting thing is that it uses block parameters for φ functions instead of a `phi`-like instruction.

```llvm
fn i32 @loopFactorial(i32) fastcc {
entry(i32 %n):
  %0 = iconst i32 1
  br loop.head(i32 %n, i32 %n)

loop.head(i32 %x, i32 %y):
  %1 = icmp eq i32 %x, %0
  condbr bool %1, loop.body, exit(%y)
  
loop.body:
  %2 = isub i32 %x, %0
  %3 = imul i32 %y, %2
  br loop.head(%2, %3)
  
exit(i32 %result):
  ret i32 %result
}
```

The details of the IR can be found [here](sir.md).

[1]: Except the back-end, that deals in a machine-specific IR instead

## Compiler Internals

Details of the compiler's inner workings can be found in the Internals section.