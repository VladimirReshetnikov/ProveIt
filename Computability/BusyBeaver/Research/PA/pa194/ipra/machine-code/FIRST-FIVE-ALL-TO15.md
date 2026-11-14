# First physical value five: all marker positions to dense 15

`PA194FirstFiveFirstCore.actualFirstCore` proves that the first non-first
marker position has a scanner delimiter when the selected value and actual
nonempty following register file are used: a selected successor gives three
zero reads before the delimiter, and selected zero gives four.
`PA194FirstFiveFirstTo15.markerFirstFiveFirstTo15` composes that fact with the
genuine marker-entry and dense-84 scanner path. Its scan-length witness,
exact endpoint tape, and model clock are stated in Lean.

`PA194FirstFiveAllTo15.markerFirstFiveAllTo15` combines this first-position
case with the separately checked seven-position result. It reaches dense 15
for all eight non-first marker positions and arbitrary selected values,
assuming the first physical value is five and the stated marker delimiter,
nonempty following file, and k=1 controller layout. The combined result
existentially quantifies the clock and endpoint tape; the branch-specific
theorems retain their exact equations. All three results hold in every
candidate PRA model, including nonstandard model values and clocks.

These are conditional physical executions from the stated intermediate
marker configuration. They do not prove blank-tape reachability, identify a
source frame, establish source-instruction simulation, or prove an iPRA
consistency implication. First physical values below five remain separate.

The three new modules passed an author suffix rebuild against previously
checked prerequisite overlays, with `propext`, `Classical.choice`, and
`Quot.sound` as their reported axioms and no `sorryAx`. The full nested
checker `check-first-five-all-to15.sh` is supplied but has not been run.
