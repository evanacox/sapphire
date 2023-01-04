# SIR Parser

Parsing SIR from input text is a effectively divided into two stages:

1. Running a [Pest](https://pest.rs/)-generated parser to get the input text into a parse tree
2. Running a dual type-checker/parser on the parse tree to generate SIR from it

The second part is the part actually implemented in the compiler.

## Preprocessing

The parser effectively runs multiple stages of pre-processing instead of walking the
parse tree a single time. This pre-processing enables use-before-definition at both the
function and the block level. 

Each time a function subtree is found, the function is *declared* and the function's body is put
onto a work list, and once every function in the file is declared the parser goes through the list
and actually parses the bodies (and properly defines the functions). 

The same is done at the basic-block level inside function bodies to make it possible to
branch to blocks that are defined after the branch instruction that targets them. This also
makes it easier to preserve the block order that was parsed, even though technically this is
irrelevant (as long as the entry block is in the right place).

What this actually means for the instruction parsing code is that all valid block/function names
are known by the time they execute, so the names not existing can only mean that the input is invalid.

## Names -> Values

The parser relies on the SSA property of the program to map names (e.g. `%x`) back to
the actual values that it has generated for those names. While this property is checked (when 
new values are introduced it's checked to make sure they did not exist before), it is checked
while instructions are being parsed. 

When an instruction or block parameter is parsed, its name (referred to by a `LocalIdent`) is
put into the `resolver` map inside of `SIRParser`. That entry is then mapped to the value referred
to by the name, so that later that value can be found. 