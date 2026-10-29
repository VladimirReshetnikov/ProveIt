# A finite primitive-recursive code for the order witness

`PRAQOrderWitnessCode` defines one arity-two finite code for
`pred(y-x)`, proves its standard evaluation and fixed-code primitive
recursiveness, and establishes its equality with the nested arithmetic
witness in every candidate-PRA equality model. Completeness gives the
closed candidate-PRA proof that this function symbol witnesses strict
order. This is one concrete witness, not general Σ₁ witnessing.

The independent replay `/tmp/pra-q-witness-code-root-62j7epul` passed both
modules without warnings and matched the author object hashes. Its three
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The driver checked the refreshed subtraction-to-Q chain's source and
object hashes and used the independently replayed order-witness provider.
Foundation, Mathlib, PRATheory and earlier code objects remain inherited
cache boundaries. The [evidence packet](pra-q-witness-code-root-replay/)
also records the clean Q-theorem translation rebuild against the refreshed
subtraction chain; its objects matched the earlier reviewed pair.
