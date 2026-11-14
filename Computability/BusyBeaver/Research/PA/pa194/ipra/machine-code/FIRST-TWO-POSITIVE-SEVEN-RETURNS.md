# First-value-two positive marker: seven return runs

`markerFirstTwoPositiveReturnSeven` in `PA194FirstTwoPositiveReturnSix.lean`
traces the positive first-value-two path through the fixed eight-block file
and back across seven model-length runs to dense state 17. The result assumes
the explicit first non-first marker layout and a blank tail, and holds in
arbitrary candidate-PRA models, including nonstandard values and run times.
It retains the left tape half as the half of a specified unary run and the
right half in terms of that run's parity and an existential value.

The supporting modules retain the full forward-scan tape shape, compose six
return runs, and join the forward and reverse scans. Lean compiled all five
new modules against retained prerequisite objects; their printed theorem
axioms contain no `sorryAx`. The nested replay wrapper was syntax checked but
not run for these modules.

The remaining controller steps to state 24, blank-start reachability, and
source-frame correspondence are open. This conditional trace does not prove
either iPRA consistency implication for the literal machine.
