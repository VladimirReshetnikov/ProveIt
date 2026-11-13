# Root check of the compact boundary-seed formula

The separate checker records that the previously audited seed `s` is
`floor((X+1)^30/(16X^15))` for `X=2^31`. I independently loaded the pinned
seed receipt and verified the equivalent integer inequalities
`s*(16X^15) ≤ (X+1)^30 < (s+1)*(16X^15)`; the tool command exited 0.
This is an exact finite arithmetic check, not a Lean proof, a complete graph
zero, or a statement about the fixed BFS coefficients.
