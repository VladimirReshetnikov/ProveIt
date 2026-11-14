# First-value-two positive marker return to state 24

`markerFirstTwoPositiveBlankTo24` in `PA194FirstTwoPositiveTo24.lean` proves
that the first non-first marker returns the literal 194-state transition table
to dense state 24 when the first register value is two and the selected value
is positive. It assumes the stated intermediate marker layout, the fixed
eight-block remaining file, and a blank tail. The result holds in arbitrary
candidate-PRA models, including nonstandard values and run times; it specifies
the final left half and existentially quantifies the time and right half.

The proof composes the forward and reverse model-length file scans with
separate final header routes for zero and successor remaining selected-run
lengths. Lean compiled the four new modules against retained prerequisite
objects; the printed theorem axioms contain no `sorryAx`. The nested replay
wrapper was syntax checked but has not been run for this change.

The zero selected-value case, blank-start reachability, and source-frame
correspondence remain open. This conditional physical trace does not prove
either iPRA consistency implication for the literal machine.
