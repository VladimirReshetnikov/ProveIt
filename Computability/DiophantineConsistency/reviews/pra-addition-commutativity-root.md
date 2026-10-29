# Candidate PRA addition commutativity

`PRAAdditionCommutativity` uses the left-zero and left-successor laws and
parameterized open induction in arbitrary candidate-PRA equality models to
prove `x+y=y+x`; completeness gives a closed candidate-theory derivation
of its universal closure. It does not by itself derive the Q order clause
or establish equivalence with a standard PRA presentation.

The independent replay `/tmp/pra-add-comm-root-l3pmwssn` passed both files
without warnings, with object hashes identical to the author build and both
axiom reports limited to `propext`, `Classical.choice`, and `Quot.sound`.
It uses the independently replayed induction and addition-law providers,
and checks current source/object hashes of their direct arithmetic inputs.
Foundation, Mathlib, PRATheory, and earlier prerequisites remain inherited
cache boundaries. Author attempts and the root run are in the
[evidence packet](pra-addition-commutativity-root-replay/).
