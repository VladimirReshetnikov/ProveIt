# Word-bound case-split experiment

The `row_le` proof in `ArithmeticProofWordBound` checks nine fixed-circuit
cases with sequential `by_cases` and rewrites. Two replacements compiled:
`split_ifs` removes 26 net lines and repeated `split` removes 18. Neither was
adopted because paired local measurements showed a substantial elaboration
cost: the four baseline runs used 6.60–7.05 seconds of user CPU, while the
two `split_ifs` runs used 21.47 and 23.35 seconds and the two repeated `split`
runs used 17.72 and 18.16 seconds. These are measurements in the recorded
cached environment, not a general benchmark of either tactic.

For the `split_ifs` variant, the target declaration, axiom and simp reports
match, and the `ArithmeticRefutationHaltBound` production client builds with
matching endpoint reports. The repeated `split` variant was compiled and timed
but did not receive the same client and interface comparisons. Both attempts,
the original proof, scripts, timings, failures and validation limitations are
preserved in [the evidence bundle](../../reviews/lean-proof-simplification-20261028-word-bound-splits-evidence/BUNDLE.json).
