# First-value-two positive marker: two return runs

`markerFirstTwoPositiveBlankAfterTwoReturns` in
`PA194FirstTwoPositiveTwoReturns.lean` continues the positive first-value-two
path from state 16 across two consecutive unary runs and back to state 17. It
assumes the fixed eight-block intermediate marker layout and a blank tail, and
holds in arbitrary candidate-PRA models, including nonstandard run lengths.

The proof preserves two nested run shapes from the six-block forward scan and
uses `PA194SixteenTwoRuns.modelSixteenTwoRuns` to follow the corresponding
physical return. The final tape halves and time are existential. Lean
compiled the four new modules against retained prerequisite objects; the
printed theorem axioms do not include `sorryAx`. The nested replay wrapper was
syntax checked but not run for these modules.

The remaining return across earlier file blocks, blank-start reachability,
source-frame correspondence, and consistency implications remain open.
