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
printed theorem axioms do not include `sorryAx`. 
The later [state-24 theorem](FIRST-TWO-POSITIVE-TO24.md) completes the
conditional positive return. Blank-start reachability, source-frame
correspondence, and consistency implications remain open.

A full nested `check-first-two-positive-two-returns.sh` replay also passed
with no `sorryAx`, rebuilding its machine-code chain against retained
prerequisite overlays.
