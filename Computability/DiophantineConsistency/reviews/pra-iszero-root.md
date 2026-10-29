# Candidate PRA zero-test code

`PRAIsZero` defines a finite primitive-recursive is-zero code and proves
in every candidate-PRA equality model, and as a closed candidate-PRA
derivation, that its value is one exactly at zero. This provides a Boolean
complement primitive for open-formula compilation; it does not itself
compile formulas or prove general witnessing.

The independent replay `/tmp/pra-iszero-root-k9akd46o` passed both modules
without warnings and matched author object hashes; both axiom reports use
only `propext`, `Classical.choice`, and `Quot.sound`. The driver checks
current source/object hashes of the refreshed nonzero and arithmetic
providers. Foundation, Mathlib, PRATheory and earlier code objects remain
inherited cache boundaries. The [evidence packet](pra-iszero-root-replay/)
preserves the author's initial namespace failure and final builds.
