# Register Allocation

Register allocators in Sapphire operate on MIR in a very specific format. This document will use x86-64
MIR syntax, but the basic idea applies to all architectures.

## Expected Input

The expectation is that the MIR input is in non-SSA form using an unlimited set of virtual registers (v-regs).

All φ nodes are expected to have already been eliminated and replaced with `mov` instructions. Effectively,
it is assumed that if the MIR was executed on a machine that had an infinite number of registers, it would
have the behavior of the original SIR. 

φ-elimination can be performed however the backend sees fit (e.g. the x86-64 backend performs critical edge 
splitting over the SIR before lowering and translates φ-nodes into naive copies), but the behavior must be modeled 
through copies (and therefore be visible to the register allocator with `MachInst::is_move`).

### Constraints

Register constraints are expected to be expressed via instructions that operate directly on specific physical 
registers. The register allocator is expected to obey these constraints. 

### Stack Frames

It is expected that the prologue/epilogue code not be present (if necessary), as the rewriter will emit
the prologue and epilogue where necessary.

### Parameters & Return Values

Parameters located in registers are the most rigid expectation the register allocator has, they are expected to be
implemented via `mov`s from physical registers into v-regs. The stack frame stores which ones are used for this. 

Return values must work in a similar way if they write to registers, they are expected to be `mov`s
from v-regs into physical registers as determined by the ABI.

Example:

```x86asm
foo:
    mov vi4, edi ; parameter `mov`s start here
    mov vi3, esi ; .
    mov vi2, edx ; .
    mov vi1, ecx ; .
    mov vi0, vi1 ; regular codegen starts here
    add vi0, vi2
    ; ...
    mov eax, vi0 ; return `mov`s start here
    ret          ; regular codegen continues here
```
