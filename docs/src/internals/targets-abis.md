# Targets, Instruction Sets, and ABIs

Sapphire divides up the different aspects of dealing with target calling conventions
into several different types/traits.

## Architectures (`Architecture`)

This models the most fundamental distinction in code generation, the actual CPU architecture
being targeted. 

Every architecture has exactly one type that implements the `MachInst` trait, and therefore
only has one MIR format. Different target ABIs are all represented in the same MIR representation.

Implementations of the `Architecture` trait:

1. `codegen::x86_64::X86_64`

## Platforms (`Platform<Arch>`)

This is a bit more specific than `Architecture`, every architecture can have many platforms
that are all for that same architecture.

The `Platform` trait models the additional info needed to generate code that's actually
usable on a given "platform" (operating environment, e.g. user-space Windows on x86-64). This
specifies what the default calling convention and stack frame convention is for the code generator
to target, and the code generator for the architecture will call into those to do platform-specific things
(e.g. call functions, allocate on the stack).

## Targets (`Target<Arch>`)

This models the architecture in addition to the actual target platform, but the platform is dynamic 
(it's a `Box<dyn Platform<Arch>>` to be specific). This was done so that the instruction selector
for an architecture does not need to be (type) parameterized, it just asks the platform (through the `Target`
it is provided) for a stack frame or calling convention and uses that for anything that's platform-specific.

This also handles type layout information, as once we know what the platform is we can determine layouts
for any type.

Targets are what code generators are parameterized with.

## ABIs

I chose to split the code that handles *calling* functions according to an ABI (`CallingConv` objects)
and the code that handles *making a function callable* according to an ABI (`StackFrame<Arch>` objects).

### Stack Frames (`StackFrame<Arch>`)

These are how the code generator manages stack layout (and parameters/return values, this is related, so
it's included in the same umbrella despite not being *exactly* related to stack layout). They just
delegate anything that's platform-specific to a `dyn StackFrame<Arch>` they've been provided
through the `Target<Arch>` given to them.

It's up to the stack frame to ensure that a function is legally callable according to the ABI it implements.

### Calling Conventions (`CallingConv<Arch>`)

These are how the code generator manages calling other functions according to the ABI that function uses.

This may not always line up with the stack frame currently being used (e.g. a `sysv` function could call a `win64` 
function), these objects are responsible for ensuring that the call will be valid.





