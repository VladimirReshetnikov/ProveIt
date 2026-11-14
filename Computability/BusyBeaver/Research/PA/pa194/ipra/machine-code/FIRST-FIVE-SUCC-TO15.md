# First physical value five: seven-position scanner handoff

`PA194FirstFiveSuccTo15.markerFirstFiveSuccTo15` follows the genuine marker
entry with first physical value five to dense 84 and composes the exact
returned-file prefix with the dense-84 scanner to dense 15. It covers the
seven non-first marker positions numbered two through eight, every selected
value, and arbitrary model-valued remaining file data. Its exact packed tape
halves, file-prefix witness, and clock are stated in Lean. It holds in every
candidate PRA model, including nonstandard values and clocks.

The marker delimiter and k=1 controller layout are hypotheses. The first
non-first position has a different returned-file prefix and is not covered;
for that position the generic delimiter parameter alone can represent an
all-zero returned tail, so more file-layout information is needed to prove a
scanner exit. These conditional paths do not establish blank-tape
reachability, identify a source frame, simulate a source instruction, or prove
an iPRA consistency implication. First physical values below five remain
separate.

The new module passed an author suffix rebuild against previously checked
prerequisite overlays, with `propext`, `Classical.choice`, and `Quot.sound`
as its reported axioms and no `sorryAx`. The full nested checker
`check-first-five-succ-to15.sh` is supplied but has not been run.
