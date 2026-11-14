# First non-first marker with positive first value

`markerFirstAtLeastOneTo24` in `PA194FirstAtLeastOneTo24.lean` shows that
the literal 194-state transition table returns the first non-first marker to
dense state 24 when the first register value is `m + 1`, for any selected
value. It assumes the explicit intermediate marker layout, the fixed
eight-block remaining file, and a blank tail. The theorem holds in arbitrary
candidate-PRA models, including nonstandard register values and run times;
it specifies the final left tape half and existentially quantifies the time
and right half.

The result joins the earlier first-at-least-two theorem with the zero and
positive selected-value cases for first value one. The positive case uses a
two-block model-length file scan and return, followed by the physical header
routes. Lean compiled the eight new modules against retained prerequisite
objects and reported no `sorryAx` in their printed theorem axioms. The nested
replay wrapper was syntax checked but not run for these modules.

The first-value-zero case, blank-start reachability, and source-frame
correspondence remain open. This is a conditional physical trace; it does not
establish either iPRA consistency implication for the literal machine.
