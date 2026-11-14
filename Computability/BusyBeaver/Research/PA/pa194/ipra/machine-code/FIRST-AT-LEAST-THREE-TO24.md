# First non-first marker with first value at least three

`markerFirstAtLeastThreeTo24` in `PA194FirstAtLeastThreeTo24.lean` combines
the first-value-three, first-value-four, and at-least-five results. For the
first non-first marker, a fixed eight-block remaining file, the explicit
marker layout, and a blank file tail, it returns the physical table to dense
state 24 for any selected value whenever the first value is `m + 3`.

The theorem holds in arbitrary candidate-PRA models, so `m`, the selected
value, other register values, and the witnessing time may be nonstandard.
The resulting left tape half is specified; the right half and time are
existential. Lean checked the combined module against previously checked
prerequisite objects and reported no `sorryAx`. A full nested replay of
`check-first-at-least-three-to24.sh` also passed, rebuilding the machine-code
chain against retained prerequisite overlays with no `sorryAx`.

This is conditional on an intermediate marker configuration. It does not
show that a blank-start machine reaches that configuration, identify the
physical run with the source scheduler, or establish a PA consistency
equivalence in iPRA.
