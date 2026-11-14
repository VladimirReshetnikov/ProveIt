# First-value-four marker return through state 24

`markerFirstFourAllTo24` in `PA194FirstFourAllTo24.lean` shows that the
first non-first marker returns the physical 194-state table to dense control
state 24 when the first register value is four, for every selected value.
It assumes the explicit marker layout and a blank tail after the finite
remaining file. The conclusion gives the resulting left tape half and an
existential right half and time. All values and times may be nonstandard in
an arbitrary candidate-PRA model.

The proof joins the previously verified zero-selected path with the positive
case in `PA194FirstFourPositiveTo24.lean`. For positive values that module
traces both remaining-length cases through their exact state-13 and state-16
shapes, returning to the same header at state 24. Lean compiled both modules
against previously checked prerequisite objects and printed no `sorryAx` in
the theorem dependencies. The nested wrapper was syntax checked but not run
for these two modules.

This is a conditional segment of the physical table. It does not establish
blank-start reachability, a source-frame simulation, or either iPRA
consistency implication for the literal machine.
