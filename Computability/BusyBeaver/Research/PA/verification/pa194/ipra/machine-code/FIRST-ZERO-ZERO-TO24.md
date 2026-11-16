# First-value-zero, zero-selected marker return to state 24

`markerFirstZeroZeroBlankTo24` in `PA194FirstZeroZeroTo24.lean` proves that
the first non-first marker returns the literal 194-state transition table to
dense state 24 when both the first register and selected value are zero. It
assumes the explicit intermediate marker layout, the fixed eight-block file,
and a blank tail. The theorem holds in arbitrary candidate-PRA models,
including nonstandard file values and run times; it specifies the final left
half and existentially quantifies the time and right half.

The new modules follow the state-46 and state-110 boundaries, the file carry
and return, and the final header route. Lean compiled all nine modules against
retained prerequisite objects; the printed theorem axioms contain no
`sorryAx`. The nested replay wrapper was syntax checked but not run for this
change.

The positive selected-value branch was subsequently combined with this case
in [the all-value return](FIRST-ALL-TO24.md). Blank-start reachability and the
source-frame correspondence remain open. These conditional traces do not
establish either iPRA consistency implication for the literal machine.
