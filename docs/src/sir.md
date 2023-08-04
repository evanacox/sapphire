# Sapphire IR (SIR) Reference

```other
type %boxed.i32 = { ptr }  
  
fn ptr @boxed.allocate(i64 %0)  
  
fn { ptr } @boxed.add.i32({ ptr } %0, { ptr } %1) {  
entry:  
    %2 = extract ptr, { ptr } %0, 0  
    %3 = extract ptr, { ptr } %1, 0  
    %4 = load i32, ptr %2  
    %5 = load i32, ptr %3  
    %6 = iadd i32, %4, %5  
    %7 = iconst i64, 4  
    %8 = call @boxed.allocate(i64 %7)  
    store i32 %6, ptr %8  
    ret ptr %8  
}
```

## Structure

## Memory Model

### Bytes, Fundamental Sizes

Bytes in SIR are 8-bit, all integers are 2's complement and have bit-width/sizes that are powers of two.

### Alignment

All objects are aligned to powers of 2. Unaligned access is undefined behavior, unless it is through specific means provided by the IR.

Formally, the alignment \\( A \\) of any object \\( O \\) is an integer \\( 2^N \\) such that \\( N \in \mathbb{N} \\).

### Memory & Reachability

The memory available to a program is considered to be an array of `i8` of an unspecified length. Each byte in memory is initially considered to be unreachable.

A given *section* (a contiguous subset of the larger available memory) of memory is considered to be *reachable* if one of the following conditions is true:

1. The memory has been returned from an implementation-defined *allocation function*, such as `malloc` , `alloca` or `::operator new`.
2. A pointer to the memory is made available to the program through the IR, i.e. a global was used (globals are available to the program as `ptr` values), an `alloc` instruction evaluated to a given `ptr`, etc.
3. The implementation exposes the memory through known integral addresses (e.g the implementation guarantees that all memory is ‘reachable’ because its freestanding, the implementation guarantees that a section is available at address `0xdeadbeef`, etc.)

### Object Storage

A given section of memory can be used as the *storage* of an object, however SIR does not enforce any restrictions to what can be stored in a given section based on type alone (other than that the size of the object must be \\( \le \\) the size of the section).

Storage is simply considered to be a set of bytes that happen to store a given set of values.

## Types

### Function Signatures

These are not quite "types"

### Aggregates v. Primitives

*Primitive* types are the atomic values of the IR, e.g. integers, booleans, floats and the like. *Aggregates* are complex types that are made up of one or more primitives (or other aggregates). Each value that is contained in an aggregate is said to be a *member* the aggregate, with each member being identified by an index (starting at zero).

### `bool`: Booleans

`bool` models the pure idea of a boolean, with two states: `true` and `false`.

They are not 'integers' as they are in LLVM and some other IRs, although they can be

converted into integers and back easily with the `btoi` and `itob` instructions.

All `bool`s are exactly byte sized and byte aligned, i.e. they are equivalent to an `i8`

in size, alignment, and other storage expectations.

### `iN`: Integers

`iN` models the concept of two's complement integers, and acts the same way that

integers do on the vast majority of computers. Unlike integers in most languages, they

are sign-less. Note that this does not mean *unsigned*, instead, sign is determined by the

instruction. This more closely models the hardware, and allows more granular control over

the behavior / guarantees that are desired.

Integers are in the form `iN`, such that \\( N \in \{8, 16, 32, 64\} \\). Support for

wider integers (i.e. `i128`) or arbitrary-width integers (i.e. `i37`) may come in the future.

The size of an integer is exactly as many bytes as is required to store \\( N \\) bits,

and the alignment of an integer is exactly the same as its size.

The endianness of integers is unspecified, but is defined by a given target.

### `fN`: Floats

`fN` model floating-point numbers that follow the IEEE-754 standard. Currently, only two

are supported:

- `f32`: IEEE single-precision, i.e. `binary32`
- `f64`: IEEE double-precision, i.e. `binary64`

In the future, others may be supported (e.g. `f128` for IEEE quads).

The size of a float is exactly as many bytes as is required to store \\( N \\) bits,

and the alignment of a float is exactly the same as its size.

### `ptr`: Pointers

`ptr` models the idea of a pointer, and nothing else. Unlike many high-level languages, pointers

are untyped.

### `[T, N]`: Arrays

`[T, N]` models contiguous blocks of storage, approximately equivalent to arrays in C. Arrays are considered to be aggregate types, and thus aggregate operations can be used on them. Each array index is considered to be a distinct aggregate member.

an independent element.

They take up exactly `sizeof(T) * N` bytes of storage, with alignment that is equal to `alignof(T)`.

Note that this means that arrays that satisfy one of the following conditions are zero-sized:

- `N == 0`
- `sizeof(T) == 0`

```other
[i8, 0]  
[{}, 64]  
[i64, 512]  
[[[i64, 16], 16], 16]
```

### `{ T... }`: Structures

`{ T... }` models a `struct` in C, and conform to the same ABI as C structures would for a given target. They are aggregate types, and thus each member of the structure is one member of the aggregate and can be accessed using aggregate instructions. Members are indexed according to their order, i.e. given the structure `{ ptr, i32, f64 }`, `ptr` is at index `0`, `i32` is at index `1`, and so on.

Structures are padded, and their size is thus determined by the order of each element, and the size/align of each element. Note that structures satisfying one of the following conditions are zero-sized:

- No elements
- Every element is zero-sized

```other
{ ptr, i64, i64 }  
{ }  
{ i32, i32 }, f64, [i8; 64] }
```

# Functions

Functions are made up of a name, a call signature, a list of stack slots, and a list of basic blocks.

## Call Signature 

### Return Value

The return value can have the `noalias` and `nonnull` attributes. They work the same as with arguments.

### Function Arguments

Function arguments can have a type and an attribute list, the following attributes exist and can all only
be applied to pointers.

#### `noalias`

This says that a pointer will not alias with any other pointers accessible to the function it is passed to, i.e.
there is no way it can get another pointer that aliases the same memory (without `itop`/`offset`/etc). 

> > If the function does get memory that aliases the `noalias` pointer, the behavior is undefined.

#### `nonnull`

This says that the pointer is guaranteed to not be null.

> > If the pointer is null, the behavior is undefined.

#### `byval(<n>)`

> > Note: This attribute is not intended for public use. 
> > 
> > The reason is that this exists exclusively  for internal ABI legalization code to generate, 
> > not for user code to generate.
> > 
> > If you want to get this behavior, just pass an aggregate type by-value and the backend will handle it. 

This is a way of encoding a specific ABI constraint, i.e. "by-value" passing on the stack. 

When this is used, any callers are expected to push `<n>` bytes onto the stack, the pointer value
itself is the beginning of that stack allocation.

# Stack Slots

Stack slots are how stack memory is allocated in SIR. They explicitly mark all the (static) stack memory that will
be needed by a function, all this memory is allocated before the entry block of a function is entered.

```other
$name = stack T
```

`T` is what defines the specific stack slot, as the slot is allocated to have exactly enough space for a `T`, and
has the correct alignment for a `T`. 

> > Note: While data of types besides `T` can be stored into/read from the slot, the type of the data must
> > fit within the layout bounds of `T`. Do keep in mind that doing so will prevent the data from being 
> > promoted into virtual registers. 
> >
> > If it does not, the behavior is undefined due to out-of-bounds accesses or unaligned accesses.

Pointers into this memory are obtained through the `stackslot` instruction, which yields a `ptr` to a specified slot.

Stack memory is not guaranteed to be maintained unless it escapes a function, it simply provides a way for languages
like C to easily represent variables and whatnot. Stack memory can be legally promoted into SSA values provided
the pointer value is not observed in any way (i.e. is not used in any way besides either `load`ing from that memory
or `store`ing to that memory).

Consider this implementation of `max` in C:

```c
int max(int x, int y) {
    if (x < y) {
        return y;
    } else {
        return x;
    }
}
```

A C frontend could translate it naively into code that uses stack slots for every variable and 
the return value, and simply generates loads/stores when those values are accessed/modified. This
allows the front-end to be **much** simpler, and the middle-end can use the correct algorithms
it already has to promote these values into registers where possible. 

One such translation looks like this:

```other
fn i32 @max(i32, i32) {
  $x = stack i32
  $y = stack i32
  $ret = stack i32
  
entry(i32 %0, i32 %1):
  %x = stackslot $x
  %y = stackslot $y
  %ret = stackslot $ret
  store i32 %0, ptr %x
  store i32 %1, ptr %y
  %5 = load i32, ptr %x
  %6 = load i32, ptr %y
  %7 = icmp slt i32 %5, %6
  condbr bool %7, if.then, if.else
  
if.then:
  %8 = load i32, ptr %y
  store i32 %8, ptr %ret
  br exit
  
if.else:
  %9 = load i32, ptr %x
  store i32 %9, ptr %ret
  br exit
  
exit:
  %10 = load i32, ptr %ret
  ret i32 %10
}
```

While this is very ugly code, it's also very fast for a front-end to generate and is obviously correct. This
can then be optimized by Sapphire with `mem2reg` (the stack -> register promotion pass) into the code that the 
front-end wanted:

```other
fn i32 @max(i32, i32) {
entry(i32 %x, i32 %y):
  %0 = icmp slt i32 %x, %y
  condbr bool %7, if.then, if.else
  
if.then:
  br exit(i32 %y)
  
if.else:
  br exit(i32 %x)
  
exit(i32 %ret):
  ret i32 %ret
}
```

Other optimizations could turn this into `sel`, but the initial transform into SSA values (and therefore virtual registers)
is the key one. 

# Basic Blocks

A basic block is a container for a list of instructions, all of which are executed in the order they appear in a given block.

This effectively makes basic blocks a small-scale linear IR, since a given basic block contains exclusively IR that is executed linearly without branching.

```other
; implements the quadratic formula, given f64 %a, f64 %b and f64 %c
block: 
  %0 = fneg f64 %b                    ; -b
  %1 = fconst f64 2.0
  %2 = call f64 @pow(f64 %b, f64 %1)  ; b^2
  %3 = fmul f64 %a, %c                ; ac
  %4 = fconst f64 4.0
  %5 = fmul f64 %3, %4                ; 4ac
  %6 = fsub f64 %2, %5                ; b^2 - 4ac
  %7 = call f64 @sqrt(f64 %6)         ; sqrt(b^2 - 4ac)
  %8 = fmul f64 %a, %1                ; 2a
  %9 = fadd f64 %0, %7                ; -b + sqrt(b^2 - 4ac)
  %x1 = fdiv f64 %10, %1              ; (-b + sqrt(b^2 - 4ac)) / 2.0
  %10 = fsub f64 %0, %7               ; -b - sqrt(b^2 - 4ac)
  %x2 = fdiv f64 %10, %1              ; (-b - sqrt(b^2 - 4ac)) / 2.0
  ; x1 = + solution
  ; x2 = - solution
```

Basic blocks have exactly one *terminator*, these are the last instruction in a given basic block. They are some sort of branching-ish instruction that moves control somewhere else.

Basic block can also contain one or more *parameters*, these implement the φ (`phi`) function found in SSA-based IRs. When
jumping to a block with a parameter, different control flow paths can pass different values for the parameter, effectively
implementing `phi`s while automatically enforcing the ideal `phi` properties just through the structure of the IR. 

> > Note: This avoids the usual special-casing of instructions in transform passes, LLVM has to treat `phi` as magic
> > and move it around differently than anything else, but it's still an instruction.
> >
> > This also lends well to "magic" instructions, so things like `landingpad` and `invoke` would be representable
> > in a normal way instead of adding magical rules like LLVM had to. 
 
Consider the following IR:

```other
entry:
  condbr bool %0, one, two
  
one:
  %1 = iconst i32 16
  br merge(%1)

two:
  %2 = iconst i32 24
  br merge(%2)

merge(i32 %3):
  ret i32 %3
```

It correctly implements the following C code:

```c
int x;

if (%0)
    x = 16;
else
    x = 24;

return x;
```

# Instructions

## Miscellaneous

### '`call`‘ - Call Function

Calls a function, passing zero or more arguments to that function and eventually returning when the called function returns.

```other
fn i32 @add(i32, i32)

fn void @do_something()

fn i32 @something_else() {
%entry:
  %0 = call i32 @add(i32 0, i32 1)
  call void @do_something()
  ret i32 %0
}
```

Calls to `void` functions cannot be bound to a name, as they do not really have a 'value’.

Syntax:

```other
(<val> =)? call <ty> <fn-name>((<ty> <val>) (, <ty> <val>)*)
```

### '`indirectcall`' - Indirect Call

Calls a function pointer. Otherwise, equivalent to `call` but taking a function type and a pointer 
instead of taking the name of a (declared) function.

```other
%0 = globaladdr @printf
%1 = globaladdr @some_string
%2 = iconst i32 42
%1 = indirectcall i32 (ptr, ...), ptr %0(ptr %1, i32 %2)
```

Syntax:

```other
(<val> =)? call <fn-sig>, <ty> <val>((<ty> <val>) (, <ty> <val>)*)
```

### '`icmp`‘ - Integral Comparison

Compares two given integer, boolean or pointer values using a given comparison operation, and returns a `bool` representing the result of the comparison.

```other
%0 = icmp eq i32 %a, %b
%1 = icmp sgt i32 %a, %b
%2 = and bool %0, %1
condbr bool %2, if.true, if.false
```

There are several possible comparisons:

| Opcode | Operation              |
|--------|------------------------|
| `eq`   | \\( = \\)              |
| `ne`   | \\( \ne \\)            |
| `ugt`  | \\( > \\) (unsigned)   |
| `ult`  | \\( < \\) (unsigned)   |
| `uge`  | \\( \ge \\) (unsigned) |
| `ule`  | \\( \le \\) (unsigned) |
| `sgt`  | \\( > \\) (signed)     |
| `slt`  | \\( < \\) (signed)     |
| `sge`  | \\( \ge \\) (signed)   |
| `sle`  | \\( \le \\) (signed)   |

> > Note that for `icmp` using `bool`s, `true` acts as-if it was the value `1` and `false` acts as-if it was the value `0`. This means that `true > false` whether the comparison is signed or unsigned.

Syntax:

```other
<val> = icmp <opcode> <ty> <val>, <val>
```

### ‘`fcmp`‘ - Floating-point Compare

Compares two given floating-point values using a given comparison operation, and returns a `bool` representing the result of the comparison.

```other
%0 = fcmp eq f32 %a, %b
%1 = fcmp ogt f32 %a, %b
%2 = and bool %0, %1
condbr bool %2, if.true, if.false
```

Comparisons can be *ordered* or *unordered.* Ordered comparisons check that neither operand is a NaN value, whereas unordered comparisons check if either operand is a NaN value.

There are several possible comparisons:

| Opcode | Operation                |
|--------|--------------------------|
| `ord`  | Ordered                  |
| `uno`  | Unordered                |
| `oeq`  | Ordered and \\( = \\)    |
| `one`  | Ordered and \\( \ne \\)  |
| `ogt`  | Ordered and \\( > \\)    |
| `olt`  | Ordered and \\( > \\)    |
| `oge`  | Ordered and \\( > \\)    |
| `ole`  | Ordered and \\( > \\)    |
| `ueq`  | Unordered or \\( = \\)   |
| `une`  | Unordered or \\( \ne \\) |
| `ugt`  | Unordered or \\( > \\)   |
| `ult`  | Unordered or \\( > \\)   |
| `uge`  | Unordered or \\( > \\)   |
| `ule`  | Unordered or \\( > \\)   |

Syntax:

```other
<val> = fcmp <opcode> <ty> <val>, <val>
```

#### '`sel`‘ - Select based on Condition

Selects one of two given values based on a `bool` condition.

```other
%0 = sel i64, bool %b, %a, %b
```

This is effectively a hint to the backend to try to use a `cmov` (x86), `csel` (arm64) or similar.

Syntax:

```other
<val> = sel <ty>, <ty> <val>, <val>, <val>
```

### Terminators

#### ‘`br`’   - Unconditional Branch

Unconditionally moves execution to another basic block.

```other
br next
```

This is effectively the `goto` construct.

Syntax:

```other
br <label>
```

#### ‘`condbr`’ - Conditional Branch

Conditionally chooses one of two branches to move execution to, depending on a `bool` condition.

```other
; equivalent to the following C code:
; 
; if (%0) 
;   goto %if.true;
; else 
;   goto %if.false;
; 
%0 = iconst i32 0
%1 = icmp eq i32 %x, %0
condbr bool %1, if.true, if.false
```

`condbr` is only able to branch based on `bool` values. The first branch is always taken for a `true` value, and the second is always taken for a `false` value.

`if.true` and `if.false` cannot be the same block (even with different arguments), they must be different blocks.

Syntax:

```other
condbr <ty> <val>, <label1>( (<args>) )?, <label2>( (<args>) )?
```

#### ‘`unreachable`‘ - Unreachable instruction

Similar to `__builtin_unreachable`: Effectively asserts that the end of the block cannot be reached in a valid program. If the containing block is reached and the `unreachable` is executed, the program's behavior is undefined.

```other
unreachable
```

> > This can be used for aggressive optimizations, as blocks that have `unreachable` as their terminator and do not call any other functions can be optimized into a block only containing `unreachable`, and any branches that go to an empty (except for `unreachable`) block can be assumed to be never taken.

This can lead to some extremely aggressive transformations. `unreachable` is effectively "viral,” one block containing it can "infect" many blocks that go to it (directly or not).

When optimizations are enabled, branches that are determined to be unreachable may be removed, or may remain as blocks that simply contain `unreachable`.

When the actual compilation step is performed, `unreachable` may be transformed into a trap instruction, or the block may simply be removed if it was unable to be removed during optimization.

#### ‘`ret`‘ - Return

Returns from a function to a given caller.

```other
ret i32 64
```

`ret` can return either `void` (in which case nothing is returned), or a value of a given type.

Syntax:

```other
ret ((void) | (<ty> <val>))
```

### Bitwise Operations

#### ‘`and`’ - Bitwise AND

Performs a bitwise AND between two integer or boolean values.

```other
%0 = and i32 %x, %y
```

The operands must have the same type. For booleans, this is equivalent to `%x && %y`. For integers, each bit position in the new value is calculated using the AND truth table.

Syntax:

```other
<result> = and <ty> <val>, <val>
```

#### ‘`or`’ - Bitwise OR

Performs a bitwise OR between two integer or boolean values.

```other
%0 = or i32 %x, %y
```

The operands must have the same type. For booleans, this is equivalent to `%x || %y`. For integers, each bit position in the new value is calculated using the OR truth table.

Syntax:

```other
<result> = or <ty> <val>, <val>
```

#### ‘`xor`’ - Bitwise XOR

Performs a bitwise XOR between two integer or boolean values.

```other
%0 = xor i32 %x, %y
```

The operands must have the same type. For booleans, this is equivalent to `%x != %y`. For integers, each bit position in the new value is calculated using the XOR truth table.

Syntax:

```other
<result> = xor <ty> <val>, <val>
```

#### ‘`shl`’ - Shift Left

Shifts a given value left by a number of bits.

```other
%0 = shl i32 %a, %b
```

The operands must be the same type. Formally, this returns exactly \\( ({a \cdot 2^{b}}) \\) \\( \mathrm{mod} \\) \\( 2^{N} \\), where \\( a \\) is the first operand, \\( b \\) is the second, and \\( N \\) is the width (in bits) of the integer type.

> > It is undefined behavior if \\( b > N \\).

Syntax:

```other
<result> = shl <ty> <val>, <val>
```

#### ‘`lshr`’ - Logical Shift Right

Performs a logical (unsigned) right shift. This evaluates to the first operand shifted right by the second operand, with zero fill.

```other
%0 = lshr i32 %a, %b
```

The operands must be the same type. Formally, this returns exactly \\( ({a \cdot 2^{b}}) \\) \\( \mathrm{mod} \\) \\( 2^{N} \\), where \\( a \\) is the first operand, \\( b \\) is the second, and \\( N \\) is the width (in bits) of the integer type.

> > It is undefined behavior if \\( b > N \\).

Syntax:

```other
<result> = lshr <ty> <val>, <val>
```

#### ‘`ashr`’ - Arithmetic Shift Right

Performs an arithmetic (signed) right shift. This evaluates to the first operand shifted right by the second operand, with the sign bit of the result being filled by the sign bit of the first operand.

```other
%0 = ashr i32 %a, %b
```

The operands must be the same type.

> > It is undefined behavior if \\( b > N \\), where \\( b \\) is the second operand, and \\( N \\) is the width (in bits) of the operand type.

Syntax:

```other
<result> = ashr <ty> <val>, <val>
```

### Integer Arithmetic

#### ‘`iadd`’ - Integer Addition

Returns the sum of the two arguments.

```other
%0 = iconst i32 32
%1 = iconst i32 4
%2 = iadd i32 %0, %1
```

#### ‘`isub`’ - Integer Subtraction

Returns the difference of the two arguments.

```other
%0 = iconst i32 32
%1 = iconst i32 4
%2 = isub i32 %0, %1
```

#### ‘`imul`’ - Integer Multiplication

Returns the product of the two arguments.

```other
%0 = iconst i32 32
%1 = iconst i32 4
%2 = imul i32 %0, %1
```

#### ‘`udiv'` - Integer Division (Unsigned)

Returns the quotient of the unsigned division of the two arguments.

```other
%0 = iconst i32 32
%1 = iconst i32 4
%2 = udiv i32 %0, %1
```

#### ‘`sdiv`’ - Integer Division (Signed)

Returns the quotient of the unsigned division of the two arguments.

```other
%0 = iconst i32 32
%1 = iconst i32 4
%2 = sdiv i32 %0, %1
```

#### ‘`urem`’ - Integer Remainder (Unsigned)

Returns the remainder of the unsigned division of the two arguments.

```other
%0 = iconst i32 32
%1 = iconst i32 4
%2 = urem i32 %0, %1
```

#### ‘`srem`’ - Integer Remainder (Signed)

Returns the remainder of the signed division of the two arguments.

```other
%0 = iconst i32 32
%1 = iconst i32 4
%2 = srem i32 %0, %1
```

### Floating-Point Arithmetic

#### ‘`fneg`’ - Floating-point Negation

Returns the negation of a floating-point value.

```other
%0 = fconst f64 -1.2
%1 = fneg f64 %0
```

#### ‘`fadd`’ - Floating-point Addition

Returns the sum of the two floating-point values.

```other
%0 = fconst f64 -1.2
%1 = fconst f64 5.5532309
%2 = fadd f64 %0, %1
```

#### ‘`fsub`’ - Floating-point Subtraction

Returns the difference of the two floating-point values.

```other
%0 = fconst f64 -1.2
%1 = fconst f64 5.5532309
%2 = fsub f64 %0, %1
```

#### ‘`fmul`’ - Floating-point Multiplication

Returns the product of the two floating-point arguments.

```other
%0 = fconst f64 -1.2
%1 = fconst f64 5.5532309
%2 = fmul f64 %0, %1
```

#### ‘`fdiv`’ - Floating-point Division

Returns the quotient of the floating-point division on the two arguments.

```other
%0 = fconst f64 -1.2
%1 = fconst f64 5.5532309
%2 = fdiv f64 %0, %1
```

#### ‘`frem`’ - Floating-point Remainder

Returns the remainder of the floating-point division on the two arguments.

```other
%0 = fconst f64 -1.2
%1 = fconst f64 5.5532309
%2 = frem f64 %0, %1
```

### Memory

#### '`alloca`‘ - Dynamically Allocate in Stack Frame

Allocates memory in the current function’s stack frame. The memory is always automatically returned when the function in which the memory was allocated returns to its caller.

> > This is effectively the `alloca` function in C.

```other
%0 = alloca [i64, 512]
```

Syntax:

```other
<val> = alloca <ty>
```

#### ‘`load`’ - Load Value from Address

Loads a value of a given type from a given address.

```other
; equivalent C code:
;
;   int32_t x = *((int32_t*)p);
; 
%x = load i32, ptr %p
```

Syntax:

```other
<result> = load (volatile)? <ty>, <ty> <val>
```

Given `load T, ptr %p`, the pointer `%p` must be valid and point to an allocation of least `sizeof(T)` bytes.

> > It is undefined behavior to store to a misaligned pointer, or to a pointer that points outside the bounds of objects allocated by the program.

A load can be marked as `volatile`, which signals that the load must not be moved relative to any other `volatile` loads or stores (or any operations that could potentially execute `volatile` loads or stores, e.g. calling an optimizer-opaque function). It also signals that the load cannot be omitted under any circumstances.

#### ‘`store`’ - Store Value to Address

Stores a value of a given type to a given address.

```other
; equivalent C code:
; 
;   *((int32_t*)p) = x;
; 
store i32 %x, ptr %p
```

Syntax:

```other
store (volatile)? <ty> <val>, <ty> <val>
```

Given `store T %t, ptr %p`, the pointer `%p` must be valid and point to at least `sizeof(T)` bytes.

> > It is undefined behavior to store to a misaligned pointer, or to a pointer that points outside the bounds of objects allocated by the program.

A store can be marked as `volatile`, which signals that the store must not be moved relative to any other `volatile` loads or stores. It also signals that the store cannot be omitted under any circumstances.

Example:

```other
%0 = call ptr @malloc(i64 4)
store i32 %x, ptr %0
```

#### ‘`offset`’ - Calculate Pointer Offset

Performs C-like pointer arithmetic.

```other
; equivalent C code:   
;  
;   void* new = ((int32_t*)p) + offset;  
;  
%new = offset i32, ptr %p, i64 %offset
```

There are no restrictions on what pointer values may be computed, but keep in mind that the resulting pointer may point outside the bounds of allocated objects may be misaligned, etc. Loading or storing to such addresses is undefined, but this is irrelevant to `offset`.

The second operand must be an integer. If the integer is smaller than the native pointer size, **sign-extending** occurs. If the integer is larger, truncation is performed.

### Aggregate Access

#### ‘`extract`’ - Extract Value from Aggregate

Extracts a value from an aggregate value at a given index.

```other
%0 = extract i64, { i64, i64, i64 } %obj, 0
```

The index is always a constant, even for arrays. If runtime indexing is required, the array/structure must
be stored in memory and the `offset` instruction should be used. 

Syntax:

```other
<val> = extract <ty>, <ty> <val>, <index>
```

#### ‘`insert`’ - Insert Value into Aggregate

Inserts a value into an aggregate at a given index.

```other
%0 = undef { ptr, i8, f64 } 
%1 = insert { ptr, i8, f64 } %0, f64 %x, 2
```

The index is always a constant, even for arrays. If runtime indexing is required, the array/structure must
be stored in memory and the `offset` instruction should be used.

#### ‘`elemptr`’ - Get Pointer to Element

This is the way of getting pointers to the members of in-memory aggregates.

```other
%0 = alloca { i64, i32, ptr, i8 }
%1 = elemptr { i64, i32, ptr, i8 }, ptr %0, 3
```

### Conversions

#### ‘`sext`’ - Sign-Extend Integer

Sign-extends an integer of a smaller width to one of a larger width.

```other
%0 = iconst i8 -15
%1 = sext i32, i8 %0
```

#### ‘`zext`’ - Zero-Extend Integer

Zero-extends an integer to a larger type. 

#### ‘`trunc`’ - Truncate Integer

Truncates an integer to a smaller integer type. 

#### ‘`itob`‘- Integer to Boolean

Converts an integer into a `bool`. Non-zero values ⇒ `true`, while zero ⇒ `false`

```other
%0 = iconst i32 15
%1 = itob bool, i32 %0
```

#### ‘`btoi`‘ - Boolean to Integer

Converts a boolean into an integer. `true` ⇒ `1` while `false` ⇒ `0`.

```other
%0 = bconst bool true
%1 = btoi i32, bool %0
```

#### ‘`sitof`‘- Signed Integer to Floating-point

Converts a signed integer into the nearest floating-point value. 

```other
%0 = iconst i32 -3
%1 = sitof f32, i32 %0
```

#### ‘`uitof`‘- Unsigned Integer to Floating-point

Converts an unsigned integer into the nearest floating-point value. 

```other
%0 = iconst i32 16
%1 = uitof f32, i32 %0
```

#### ‘`ftosi`‘ - Floating-point to Signed Integer

Converts a floating-point value into the nearest signed integer

```other
%0 = fconst f32 -1.2
%1 = ftosi i32, f32 %0
```

#### ‘`ftoui`‘ - Floating-point to Unsigned Integer

Converts a floating-point value into the nearest unsigned integer

```other
%0 = fconst f32 1.4
%1 = ftoui i32, f32 %0
```

#### '`fext`' - Floating-point Extend

Extends a smaller floating-point type to a larger floating-point type. 

```other
%0 = fconst f32 1.4
%1 = fext f64, f32 %0
```

#### '`ftrunc`' - Floating-point Truncate

Truncates a larger floating-point type to a smaller floating-point type.

```other
%0 = fconst f64 1.4
%1 = ftrunc f32, f32 %0
```

#### ‘`itop`‘ - Integer to Pointer

Converts an integer into a pointer with the equivalent bit-pattern. If the integer is smaller than the native pointer size, **zero-extending** occurs. If the integer is larger, truncation is performed.

```other
%1 = iconst i32 15
%0 = itop ptr, i32 %1
```

#### ‘`ptoi`‘ - Pointer to Integer

Converts a pointer into the equivalent bit-pattern in an integer. If the integer result type is smaller, truncation is performed. If the result type is larger, **zero-extending** occurs.

```other
%0 = ptoi i64, ptr %1
```

### Constant Materialization

#### '`stackslot`' - Pointer to Stack Memory

Materializes a `ptr` that points to memory allocated by a `stack` slot. These will always
produce the same `ptr` for the duration that a given function is executing (the value across
multiple calls to the function containing this is unspecified).

```other
  ; given that $x = stack i32
  %0 = stackslot $x
```

Syntax:

```other
<val> = stackslot <stack slot name>
```

#### '`globaladdr`' - Pointer to Global

Materializes a `ptr` that points to some global entity. This could be a function, a global 
variable, etc. 

```other
  ; given that fn i32 @printf(ptr, ...)
  %0 = globaladdr @printf
```

Syntax:

```other
<val> = globaladdr <global name>
```

#### '`bconst`' - Boolean Constant

Materializes a `bool` with either `true` or `false`.

```other
%0 = bconst bool true
%1 = bonst bool false
```

Syntax:

```other
<val> = bconst <ty> ((true) | (false))
```

#### '`iconst`' - Integer Constant

Materializes an integer with a given constant value. 

Integer constants are made up of digits and an optional prefix, and can be in one of four forms:

- Binary, must have prefix `0b` and is made up of `0` and `1`
- Octal, must have prefix `0o` and is made up of `[0-7]`.
- Decimal, must have no prefix and no leading zeroes and is made up of `[0-9]`. They can have a leading `-` which will make them negative.
- Hex, must have prefix `0x` and is made up of `[0-9a-zA-Z]`

Constants can be negative or positive, but they are converted to their unsigned bit-pattern regardless of sign. Since integers are two’s complement, this means that the constant `-1` is equivalent to `0xFF` or `255` for `i8`, `0xFFFF` for `i16`, etc.

```other
%0 = iconst i32 0b11
%1 = iconst i64 0xFA
%2 = iconst i8 -2
%3 = iconst i16 16
%4 = iconst i32 0o777
```

Syntax:

```other
<val> = iconst <ty> (-)?((0b) | (0o) | (0x))[0-9a-fA-F]+
```

#### '`fconst`' - Floating-point Constant

Materializes a floating-point constant from a given floating-point literal.

Floating-point literals can be in decimal form with a `.`, scientific notation, C's hex float format, or raw hex (prefix `0xfp` to make distinct from hex integer values) denoting the underlying byte values.

- Standard decimal form: `([0-9]+).([0-9]+)` (ex. `0.0039`)
- Scientific notation: `.([0-9]+)(.[0-9]+)?e(+|-)([0-9]+)` (ex. `1.749e-3`)
- Raw hex: `0xfp([0-9a-fA-F]+)` (ex. `0xfp3FD55558B21DC9EA`)
- `NaN` for an unspecified NaN value

```other
%0 = fconst f64 0xfp3FD55558B21DC9EA
%1 = fconst f32 3.14195
%3 = fconst f32 1.3e100
```

### ‘`undef`’ - Undefined Value

Materializes an uninitialized object. Reading the value yields a non-deterministic value, but it is not undefined behavior.
Reading the same `undef` value multiple times will yield the same value.

```other
%0 = undef { i32, i32 }
%1 = undef ptr
%2 = undef f64
```

### '`null`' - Null Value

Materializes a zero-ed object. Reading the value results in whatever an all-zero-bits representation means for that type.

```other
%0 = null ptr
%1 = null i32
%2 = null { ptr, i64, i64 }
```

