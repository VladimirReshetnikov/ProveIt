# First non-first marker with first value at least two

`markerFirstAtLeastTwoTo24` in `PA194FirstAtLeastTwoTo24.lean` shows that the
literal 194-state transition table returns the first non-first marker to
dense state 24 when the first register value is `m + 2`, for any selected
value. It assumes the explicit intermediate marker layout, a fixed
eight-block remaining file, and a blank tail. The result holds in arbitrary
candidate-PRA models, including nonstandard register values and run times.
The final left tape half is specified; the time and right half are existential.

The result joins the previously checked first-at-least-three cases with both
the zero and positive selected-value paths for first value two. Lean compiled
the four new modules against retained prerequisite objects and reported no
`sorryAx` in the theorem axioms. The nested replay wrapper was syntax checked
but has not been run for these modules.

This is a conditional segment of the physical table. Blank-start reachability
and the source-frame correspondence remain open; it does not establish either
iPRA consistency implication for the literal machine.
