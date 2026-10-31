# Fixed ZFC refutation: outer witness-bound reduction

`PRAWitnessClosedExistential` chooses the one or two leading witnesses of a
fixed closed formula separately in each model, assuming a `WB` bound for the
matrix. `PRAWitnessRefutationOuter` uses this to bound the actual Foundation
`provabilityPred T σ` from the positive derivation-graph bound, and then from
the positive and negative-pi bounds on `Derivation.blueprint T` in every
candidate-PRA model. It composes those hypotheses with the existing
`BoundCertificate` and no-zero comparison. `PRAWitnessZFCCertificate` applies
the same reduction to the actual Foundation ZFC refutation predicate.

The two **derivation-core witness bounds remain explicit premises**. They are
not established by this packet; it does not prove the PRA equivalence or a
uniform primitive-recursive bound code. Choosing closed existential witnesses
in Lean's metatheory does not add an axiom to candidate PRA: the final proof
existence is obtained by first-order completeness over all candidate models.

The guarded author run `/tmp/pra-refutation-outer-ofy0gdhm` passed all six
modules and axiom checks; source snapshots, full logs and terminal state are
frozen in `author-evidence/`. Its manifest pins 774 mixed-parent project/ZFC
objects and observes four current project sources; it does not prove that the
inherited objects correspond to those sources. The transitive Foundation,
ZFCinPA, Lake fallback and package ancestry remains inherited. The independent
same-parent replay `/tmp/pra-refutation-outer-k3sxlhf0` passed, matching all
six source/object/full-log rows. Its state, source snapshots and logs are in
`independent-evidence/`; it shares the same provisional ancestry.

Replay: `python3 Computability/DiophantineConsistency/reviews/pra-refutation-outer-provisional-replay/replay.py`.
