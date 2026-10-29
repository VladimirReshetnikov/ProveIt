# Conditional open-formula characteristic compiler

`PRAOpenFormulaCompiler` defines finite syntax for Boolean combinations of
equality and strict-order atoms and compiles each tree to one finite PR
code. In arbitrary candidate-PRA equality models it proves Boolean-valued
characteristic correctness, conditional on a correct Boolean equality
code. Given actual candidate-PRA derivations of the equality code's bit
and correctness sentences, completeness yields a closed correctness proof
for every encoded formula. Those two equality certificates are explicit
premises and are not proved here; coverage of all Foundation open formulas
is also separate. No general witnessing or conservation theorem is claimed.

The independent replay `/tmp/pra-open-formula-root-w4g1c006` passed both
modules without warnings, matched the author object hashes, and reported
only `propext`, `Classical.choice`, and `Quot.sound`. It used the reviewed
term and Boolean-code providers and checked the current refreshed Q-order
source/object. Foundation, Mathlib, PRATheory and earlier code providers
remain inherited cache boundaries. The [evidence packet](pra-open-formula-compiler-root-replay/)
preserves failed and warning-bearing scratch attempts without admitted
proofs, the final author run, and the refreshed Q-order snapshot.
