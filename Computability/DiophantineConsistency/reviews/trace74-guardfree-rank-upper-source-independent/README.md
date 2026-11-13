# Independent source review: guard-free signed rank upper bound

Source SHA-256 `7375f1b6a417aa4605b212fb4802fa84db74fe2418f25505e5d4067669fb243f`. The mathematical argument is consistent at its explicit scope; Lean elaboration and provider compatibility are unchecked, and no Lean was run in this review.

The first theorem is an all-commutative-ring slack identity under q=beta·J+1. For model q,beta,MC,MF,J,F,C, all variables lie in the nonnegative IΣ₁ model; J,F,C>0 and MC<beta, MF<2beta give the necessary discrete one-unit slacks after embedding. q≥1, q²−1≥0, F−1,C−1,J−1≥0 and both beta−MC−1 and 2beta−MF−1≥0 make the displayed sum nonnegative in the ordered difference ring. The identity then yields the upper inequality even when the signed rank expression is negative.

The final source specializes `ring_rank_shape` to the same 74 `masked p v` and port tuple. It assumes positive v and the two cast port bounds only; it does not assume graph zero, F<q, C≤q, F+C<q, rank nonnegativity or the guard. Rank is the actual signed difference-ring register, not a natural truncated scalar. `ι_le_ι`, casts of numerals/powers, ordered-ring instance inference, `nlinarith`/`positivity`, and the final rank-shape rewrite remain Lean elaboration risks. Full selected-provider, search-path and captured closure compatibility must be reviewed independently before a run.
