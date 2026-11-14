# First-value-one zero-selected marker return to state 24

`markerFirstOneZeroBlankTo24` in `PA194FirstOneZeroTo24.lean` proves that the
first non-first marker returns the literal 194-state transition table to dense
state 24 when the first register value is one and the selected value is zero.
It assumes the explicit intermediate marker layout, a fixed eight-block file,
and a blank tail. The proof covers arbitrary candidate-PRA models, including
nonstandard values and run times; it specifies the final left tape half and
existentially quantifies the time and right half.

The new modules trace the state-36 and state-48 boundaries, the zero-selected
file carry and return, and the final header route. Lean compiled all nine
modules against retained prerequisite objects; their printed theorem axioms
contain no `sorryAx`. The nested replay wrapper was syntax checked but not run
for this change.

The positive selected-value case for first value one, the first-value-zero
case, blank-start reachability, and the source-frame correspondence remain
open. This conditional physical trace does not establish either iPRA
consistency implication for the literal machine.
