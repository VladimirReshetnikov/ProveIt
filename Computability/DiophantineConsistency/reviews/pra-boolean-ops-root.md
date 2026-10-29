# Boolean operations in candidate-PRA models

`PRABooleanOps` proves in every candidate-PRA equality model that the
nonzero and is-zero codes return bits, that multiplying two bits implements
conjunction, and that is-zero implements negation on a bit. These are
model-level lemmas for the planned formula compiler; they are not yet
separate closed candidate-PRA derivations or a general compiler.

The independent replay `/tmp/pra-boolean-ops-root-g50rn5m9` passed both
modules without warnings and matched author object hashes; four axiom
reports use only `propext`, `Classical.choice`, and `Quot.sound`. The
driver checks current source/object hashes of the refreshed arithmetic
providers and uses the independently reviewed zero-test provider.
Foundation, Mathlib, PRATheory and earlier code objects remain inherited
cache boundaries. The [evidence](pra-boolean-ops-root-replay/) preserves
the author’s first iff-orientation failure and final builds.
