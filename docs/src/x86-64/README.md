# x86-64 Backend

This section documents the different constraints, assumptions and limitations
of the current x86-64 backend. It also documents the specific implementation
quirks of the backend.

## φ Elimination

φ elimination (also known as SSA destruction) is performed in the naive "translate into copies" method, but this has
known limitations (see lost copy problem). It is **assumed** that the `split-crit-edges` 
pass has been run over the SIR module before codegen begins, if this is not done
incorrect code can be emitted.

## Type Representation

### `bool`

`bool` is represented the same way as an `i8` (i.e. in `byte`-sized partial registers), with `false` being zero
and `true` being `1`.

## `condbr` and `icmp`/`fcmp` Interactions

Currently, the backend has two states for implementing `condbr`:

1. The comparison is the instruction directly before the `condbr`
2. The comparison is not directly before the `condbr`

This is a bit of a hack, but it's to ensure that CPU flags are maintained correctly.
The two states are implemented like so:

### Directly Before

This is how you'd want it to be emitted, a `cmp`-like instruction followed by
a jump that models the condition in the comparison. You get code like this emitted:

```x86asm
cmp rax, rdx
jl .TRUE
jmp .FALSE
```

In this case, the `icmp`/`fcmp` does **not** have a constrained register, and is
only emitted to manipulate CPU flags.

### Not Directly Before

This is the case that needs to be optimized better, but for now this is what it does. The `condbr`
places a register constraint on the comparison instruction, and it emits instructions to jump to the
true branch if that register is 1, and jump to the false branch otherwise. It effectively
generates this code:

```x86asm
test R, R
jnz .TRUE
jmp .FALSE
```

When the comparison is emitted, it is  expected to *also* emit a `set*` instruction to copy the condition 
to a register, so that the `test` previously emitted will work. The end result should look like this:

```x86asm
cmp rax, rdx
xor R, R
setle R
...
test R, R
jnz .TRUE
jmp .FALSE
```
