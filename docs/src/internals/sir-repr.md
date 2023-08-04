# SIR In-Memory Representation

SIR is represented as a (relatively obscured) graph in-memory. Representation
for a given SIR function is divided between two different types:

- `DataFlowGraph`: owns all the "things" in a function, and models data-flow between values
- `Layout`: orders the entities in a data-flow graph into lists of blocks, and lists of instructions in those blocks. 

## `DataFlowGraph`: The DFG

This is basically a massive overly-complicated lookup table. It stores lots of arenas that store everything
in a function that matters, whether it be instructions, blocks, referenced function signatures, etc. Everything
is stored inside of arenas, and 'references' to those entities is passed around by indices into those arenas. 

## `Layout`: The Layout

