# Candidate PRA left-successor addition law

`PRAAdditionSuccLeft` uses parameterized open induction in every candidate
PRA equality model to prove `succ(x)+y=succ(x+y)` and obtains an actual
closed derivation of its universal closure by first-order completeness.
This is a step toward commutativity and the Q order clause, not a proof of
standard PRA equivalence or of Parsons conservation.

The independent replay `/tmp/pra-succ-left-root-xz2_a4_i` passed both files
without warnings, with object hashes identical to the author build and both
axiom lists limited to `propext`, `Classical.choice`, and `Quot.sound`. It
uses the independently replayed open-induction and left-zero provider and
the current-source successor/addition/exhaustion objects. Foundation,
Mathlib, PRATheory, and earlier prerequisites remain inherited cache
boundaries. The [evidence](pra-addition-succ-left-root-replay/) preserves
the author attempts and the root's initial failed overlay, where a path
substitution accidentally pointed to a non-existent predecessor provider;
the subsequent successful replay uses the correct provider.
