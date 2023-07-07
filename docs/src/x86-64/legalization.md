# ABI Legalization

The x86-64 backend expects a specific subset of SIR as input.

The gist of it is the follows:

1. All aggregates that would be put into registers according to calling convention rules
   remain as aggregates in parameters
2. All other aggregates that would be passed in memory 