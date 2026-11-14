# Zero marker return through the continue-two controller

`PA194ZeroIncrementContinue.zeroIncrementToContinueTarget` composes any prior
run ending at the exact concrete increment output with the zero-first-block
controller path. `PA194MarkerZeroIncrementContinue.markerZeroToContinueTarget`
instantiates that handoff with the genuine non-first marker-entry theorem,
under the additional hypothesis `k=0`.

The marker theorem retains the original marker index and file-layout
hypotheses, the k=1 controller header, `idx+n=7`, a positive selected value,
the first physical value `k+7`, and a blank final suffix. Its model-valued
final clock and exact packed tape halves are stated in Lean. The results hold
in every candidate PRA model, including nonstandard values and clocks.

These are conditional physical paths. They do not prove the initial marker
configuration is reachable from the blank tape, that the endpoint is a
source frame, that a source instruction is simulated, or an iPRA
consistency implication.

`PA194AllFirstMarkerContinue.allFirstMarkerToContinue` combines the zero
branch with the separately proved successor branch using model zero/successor
exhaustion. Under their common marker hypotheses, it proves that every
model-valued `k` reaches dense 24 with the stated controller half and some
model-valued clock and right half. The branch-specific theorems retain their
more detailed tape equations.

The three modules passed an author suffix rebuild against previously checked
prerequisite overlays, with `propext`, `Classical.choice`, and `Quot.sound`
as their reported axioms and no `sorryAx`. The full nested checker
`check-marker-zero-continue.sh` is supplied but has not been run.
