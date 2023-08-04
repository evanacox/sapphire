# Calls

Calls are treated as-if they didn't affect the stack layout at all, and are lowered
such that they don't affect the prologue/epilogue at all. 

All calls that require stack space for parameter passing and whatnot are expected
to generate their own stack manipulation code. 

## System V

For System V, this is implemented via `push` instructions and
an `add rsp, N` after the `call` that fixes back up the stack.