# Native intuitionistic PRA decides equality with zero

`IPRAZeroStepNative.zero_decidable` proves the native theory sentence
`∀x, x=0 ∨ ¬(x=0)` without an added assumption. It transfers the proved
classical PRA `x+1=S(x)` result through the unconditional GG theorem to
obtain its double-negated equality, combines that with native successor
nonzero and Leibniz substitution to prove `x+1≠0`, and applies native
quantifier-free induction to decide equality with zero. This uses no
object-theory excluded-middle axiom.

The result does not yet prove general equality or order decidability, nor
bounded formula decidability or the equation/consistency equivalence. The
actual `PRAAddOne` local/Foundation source closure was checked against the
post-merge changes (91 resolved sources, zero intersections). The parent
object ancestry remains historical with five unrelated broad witness guards
excluded, as in the inherited manifest; external transitive ancestry remains
inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-zero-decidable-native-replay/replay.py`.

Author PASS; all five add-one/zero-step axiom reports were parsed and
contained only `propext`, `Classical.choice`, and `Quot.sound`.

Independent peer PASS; all six source/object/full-log rows match author,
and all five add-one/zero-step axiom reports contain only the standard trio.
Historical parent and excluded broad-source qualifications remain as stated.
