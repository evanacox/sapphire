window.SIDEBAR_ITEMS = {"enum":[["CallConv","Models which calling convention a given function should be emitted to follow."],["CursorPos","Models the position that the cursor is “pointing at.”"],["FCmpOp","Models the different ways that floating-point values can be compared in SIR."],["FloatFormat","Maps the hardware representation of the floating-point types to enum variants."],["ICmpOp","Models the different ways that integers values can be compared in SIR using the `icmp` instruction."],["InstData","This holds both the opcode of a given instruction and all the state that makes up that specific instruction."],["UType","An unpacked representation of a [`Type`] that takes up twice as much space, but also has Rust native `enum` semantics."],["ValueDef","Models where a given value came from."]],"fn":[["binary","A matcher that matches a binary instruction."]],"struct":[["AllocaInst","Models an `alloca` stack allocation"],["AppendBuilder","Helper type that appends to a function. Implements the [`InstBuilder`] trait to allow easy instruction creation."],["ArithmeticInst","Models a general arithmetic instruction"],["Array","Models an array type in the IR. Internally, contains a reference into the [`TypePool`] that is being used for the module being operated on."],["BConstInst","Models a `bconst` instruction."],["BasicBlock","Models a single basic block in a function within the IR."],["BasicInstMatcher","A matcher that wraps up a matcher function."],["Block","References a single basic block in the program."],["BlockIter","Allows the blocks in a layout to be iterated over in program-order."],["BlockWithParams","Models a branch target, along with any arguments being passed into that block."],["Bool","Models a boolean type in the IR."],["BrInst","Models a `br` instruction"],["CallInst","Models a direct function call to a known function"],["CastInst","Models a generalized cast instruction"],["CondBrInst","Models a conditional branch"],["DataFlowGraph","Owns all of the instructions, basic blocks, values, and everything else in a given function. Also models all the complex data-flow information between various instructions, although it does not model any of the actual code layout information (block ordering, instruction ordering, etc)."],["DebugInfo","Holds the “debug info” for an instruction, i.e. where it came from."],["ElemPtrInst","Models getting a pointer to the field of an aggregate"],["ExtractInst","Models extracting a field from an aggregate"],["FCmpInst","Models an `fcmp` instruction."],["FConstInst","Models an `fconst` instruction."],["Float","Models the `fN` class of fundamental types."],["FloatUnaryInst","Models any unary floating-point arithmetic instructions (e.g. `fneg`)"],["Func","The reference type for a [`Function`]. These can be looked up at the `Module` level."],["FuncBuilder","Helper type for building a SIR function."],["FuncCursor","Similar to [`FuncBuilder`] but for in-place modification of functions."],["FuncView","Effectively a [`FuncCursor`] without any of the operations that mutate the function."],["Function","Models a single function in the IR."],["FunctionDefinition","The definition of a function."],["GlobalAddrInst","Models aa `globaladdr` instruction."],["ICmpInst","Models a single `icmp` instruction."],["IConstInst","Models an `iconst` instruction."],["IndirectCallInst","Models an indirect call to a function stored in a pointer."],["InsertBuilder","A builder that inserts an instruction between/before other ones."],["InsertInst","Models setting a field in an aggregate"],["Inst","While [`Value`]s refer to a result of some sort, [`Inst`]s refer to the instructions themselves. This has a subtly different meaning: an [`Inst`] may not actually refer to something that produces a result."],["InstIter","Allows all of the instructions in a given block to be iterated over."],["Int","Models the `iN` class of fundamental types."],["Layout","Models the layout of an entire function and every basic-block in it."],["LoadInst","Models extracting a field from an aggregate"],["Module","Contains all the data necessary for a single module of SIR."],["ModuleContext","Models shared ownership of the state that is shared between all entities in a module."],["ModuleIdentity","Used to identify different [`Module`] instances efficiently."],["NullConstInst","Models a `null` instruction."],["OffsetInst","Models an `offset` instruction"],["ParamAttributes","Models the different attributes that can be on a given parameter."],["Ptr","Models a pointer type in the IR."],["ReplaceBuilder","A builder that replaces an instruction with a new one"],["RetAttributes","Models the different attributes that can be on a given return value."],["RetInst","Models a return from a function"],["SelInst","Models a `sel` instruction."],["Sig","The reference type for [`Signature`]s. They are keys into a table stored inside the [`DataFlowGraph`] of the function that they are used in."],["SigBuilder","Helper type for building a [`Signature`]."],["Signature","Holds all of the information necessary to call a function."],["StoreInst","Models a `store` instruction"],["Struct","Models a structure type in the IR. Internally, contains a reference into the [`TypePool`] that is being used for the module being operated on."],["Type","A reference to a type. Copyable, compact, lightweight, and can model arbitrary types in the IR."],["TypePool","Manages all of the compound types for a given module of IR."],["UndefConstInst","Models an `undef` instruction."],["UnreachableInst","Gets an `unreachable` instruction"],["Value","A basic reference to some value, either the result of some computation or an argument into a basic block. Since everything is based around function-scoped values in SIR, this is effectively equivalent to a `llvm::Value*`."]],"trait":[["BinaryInst","Some instructions model binary operations, those instructions model this trait."],["Cursor","Models basic cursor operations that view a function. None of these operations require mutable access to a given function, so they can be used inside of analyses."],["CursorMut","A cursor with additional methods for mutating the IR."],["FunctionCursorVisitor","Trait that allows configurable visiting of a single function with a [`CursorMut`]."],["GenericInstVisitor","A trait for a generic “visit an instruction” type. This is the smallest-scale visitor, as this visitor isn’t even aware of the function that a given instruction is in."],["IRMatcher","A basic matcher for a single value/instruction in the IR."],["InstBuilder","Helper trait that allows easy creation of instruction builders. This trait provides a variety of helper methods that build instructions and inserts them in whatever way the trait implementor defines."],["Instruction","These are the properties that any transform or analysis pass needs to be able to observe for any given instruction in any block."],["SIRVisitor","Trait that allows configurable and simple SIR visiting."],["Terminator","Models a terminator, i.e. the only instructions that are allowed at the end of a basic block."],["UnaryInst","Some instructions model unary operations, those instructions model this trait."]],"type":[["ArithInst","Models a general arithmetic instruction that isn’t commutative (e.g. `isub`, `sdiv`)"],["CommutativeArithInst","Models a general arithmetic instruction that is commutative (e.g. `iadd`, `imul`)"]]};