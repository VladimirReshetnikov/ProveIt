# Conditional native iPRA equation comparison

`mapped_noZero_comparison_with_target` assembles the literal intuitionistic
universal negated-equality no-zero sentence from three explicit premises:

1. Native iPRA proves the GG image of every classical PRA axiom.
2. Classical PRA proves the mapped no-zero iff negation of a sentence ψ.
3. Native iPRA proves the equivalence between `∼ψᴺ` and a target sentence.

The theorem does not establish these premises or identify the target with
ZFC consistency. It uses the existing generic proof translation and the
independently replayed iff/neg helper, rebuilding the former on that coherent
parent. External transitive ancestry is inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-conditional-comparison-replay/replay.py`.

Author PASS; the three endpoint axiom reports were separately parsed and
contained only `propext`, `Classical.choice`, and `Quot.sound`.

Independent peer PASS; all six source/object/full-log rows match author,
and all three endpoint axiom reports contain only the standard Lean trio.
