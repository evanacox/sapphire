window.SIDEBAR_ITEMS = {"fn":[["compute_postorder","Directly computes a valid post-ordering of the blocks in `func`’s control-flow graph."],["print_module","Prints an entire module to `stdout`."],["stringify_module","Writes an entire module to a [`String`]."]],"struct":[["ControlFlowGraph","Models successor/predecessor information about the control-flow graph of a given function."],["ControlFlowGraphAnalysis","An analysis pass that wraps up a [`ControlFlowGraph`] into something that can actually be used inside of transform passes."],["DominanceFrontier","Models the dominance frontier information for a function."],["DominanceFrontierAnalysis","Wrapper analysis that generates a [`DominanceFrontier`]."],["DominatorTree","Models the dominator tree for a given control-flow graph. This analysis also gives a reverse postorder for the blocks in the CFG (as this is required for calculating dominators, and is useful information for other passes to have as well)."],["DominatorTreeAnalysis","Wrapper analysis that generates a [`DominatorTree`]."],["ModuleStringifyAnalysis","This is an analysis that provides a [`ModuleWriter`] to any code that wants it."],["ModuleWriter","A simple SIR -> text pass that takes in an entire module, turns it into textual SIR, and then maps each IR entity to a range of text referring to it."]]};