# Compile candidate-language terms to finite PR codes

`PRATermCompilation.compileTerm` structurally compiles every term with n
bound inputs and no free variables to one arity-n finite primitive-recursive
code. Each compiled code has a primitive-recursive standard evaluation.
`modelCompile` proves its equality to the term in every candidate-PRA
equality model, using the actual projection and composition equations;
completeness yields a closed candidate-PRA derivation of the universally
closed equality. This does not normalize arbitrary formulas or supply
general Σ₁ witnessing or conservation.

The independent replay `/tmp/pra-term-compilation-root-e3225g5_` passed
both modules without warnings, matched author objects, and reported only
`propext`, `Classical.choice`, and `Quot.sound`. The driver checks current
source/object hashes of the direct arithmetic providers. Foundation,
Mathlib, PRATheory and earlier code providers remain inherited cache
boundaries. The [evidence packet](pra-term-compilation-root-replay/) retains
the first author build's unused-simp warning and the clean final build.
