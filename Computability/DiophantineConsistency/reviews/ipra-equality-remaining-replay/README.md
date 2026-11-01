# Remaining equality obligations for native iPRA

The coherent replay rebuilds the verified images of all three basic axioms on
the independently replayed equality-reflexivity parent. Native induction, all
defining equations and all basic axioms are thus discharged in the conditional
comparison. `equality_images_from_remaining` separately identifies the four
remaining equality image families: symmetry, transitivity, arbitrary-arity
function congruence and arbitrary-arity relation congruence. Classical
equation comparison and consistency-target equivalence are still explicit
premises. External transitive ancestry is inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-equality-remaining-replay/replay.py`.

Author PASS; all three endpoint axiom reports were separately parsed and
contained only `propext`, `Classical.choice`, and `Quot.sound`.

Independent peer PASS; all four source/object/full-log rows match author,
and all three endpoint axiom reports contain only the standard Lean trio.
