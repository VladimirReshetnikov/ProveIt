# First-value-four positive marker return through state 15

`markerFirstFourPositiveBlankTo15` in `PA194FirstFourPositiveTo15.lean`
continues the physical-table run from the first non-first marker to dense
state 15. It assumes first register value four, a positive selected value,
the stated marker layout, and a blank tail after the fixed finite file. The
proof covers arbitrary candidate-PRA models, including nonstandard register
lengths and run times.

The returned tape halves at state 13 are even in both cases for the remaining
selected-block length, allowing the physical transitions through states 14
and 15. The final theorem records existential tape halves. The later [all-selected theorem](FIRST-FOUR-ALL-TO24.md) returns this
conditional path to state 24; the source-frame and blank-tape connections
remain open.

Lean compiled the module against previously checked prerequisite objects, with
no `sorryAx` in the printed theorem axioms. It was also rebuilt successfully
in the full nested `check-first-at-least-three-to24.sh` replay using retained
prerequisite overlays. This conditional trace
does not establish either consistency implication for the literal machine.
