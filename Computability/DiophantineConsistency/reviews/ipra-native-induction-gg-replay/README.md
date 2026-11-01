# Native iPRA induction axiom GG transfer

`IPRAInductionNativeGG.induction_scheme_gg` proves unconditionally that
`IPRANativeTheory.nativeTheory` proves the GG image of every axiom in the
actual Foundation open-induction schema over the PR language. The proof
rebuilds the full affected induction chain on the independently replayed
native-theory parent, avoiding a mixed overlay of project objects.

Defining, equality and basic classical PRA axiom transfers and the actual
consistency-side translation remain separate obligations; no iPRA equivalence
for the Diophantine equation is claimed. External transitive ancestry is
inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-native-induction-gg-replay/replay.py`.

Author PASS; all six final-comparison and specialization axiom reports were
separately parsed and contain only the standard Lean trio.

Independent peer PASS; all twelve source/object/full-log rows match author.
All six axiom reports contain only the standard Lean trio.
