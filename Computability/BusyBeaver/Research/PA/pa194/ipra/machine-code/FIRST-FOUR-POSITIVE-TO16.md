# First-value-four positive marker return through state 16

`markerFirstFourPositiveBlankTo16` in `PA194FirstFourPositiveExact.lean`
continues the physical-table run from the first non-first marker to dense
state 16. It assumes first register value four, a positive selected value,
the stated marker layout, and a blank tail after the fixed finite file. The
proof holds in arbitrary candidate-PRA models, including nonstandard values
and times.

`selectedZeroExact` and `selectedSuccExact` export exact state-13 tape
formulas for the two cases of the remaining selected-block length. The module
uses these formulas to apply the existing header controller through state 16.
The final marker theorem records existential tape halves. Further work is
needed to return the physical control to state 24 and to connect the run to
the blank tape and the source-level machine.

Lean compiled this module against previously checked prerequisite objects;
the printed theorem axioms do not include `sorryAx`. The nested replay
wrapper has been syntax checked but not run for this module. The theorem does
not establish either consistency implication for the literal machine.
