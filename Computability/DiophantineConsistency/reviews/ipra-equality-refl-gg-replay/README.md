# GG image of classical equality reflexivity

The actual Foundation equality reflexivity axiom has a GG proof in native
intuitionistic PRA, using native reflexivity and double-negation introduction
under universal closure. This requires no equality decidability. Symmetry,
transitivity, arbitrary-arity function congruence and relation congruence
remain separate obligations; no full equality transfer or final equation
equivalence is asserted. External transitive ancestry is inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-equality-refl-gg-replay/replay.py`.

Author PASS; the axiom report was separately parsed and contains only
`propext`, `Classical.choice`, and `Quot.sound`.

Independent peer PASS; source/object/full-log rows match author and the
axiom report contains only the standard Lean trio.
