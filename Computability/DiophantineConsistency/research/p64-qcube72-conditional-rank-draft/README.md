# Conditional main-index/rank identification for a 72 zero

[`FreeMainConditionalRank.main_index_eq_rank`](FreeMainConditionalRank.lean)
passed its [guarded Lean check](observations/attempt01/result.json). In any
`IΣ₁` model, given an actual positive 72-graph zero with `q≥33`, it concludes
that the main Pell coordinates are at an explicitly supplied positive rank
`R`, **provided** the caller also supplies `2R<c` and the strong and
absolute-difference auxiliary norm identities displayed in the theorem.
The supplied `R` is arbitrary in this theorem: it is not yet bound to the
graph's rank expression. The proof uses the checked actual-zero large-c
result and the existing signed-half-index theorem.

Lean exited 0, with `[propext, Classical.choice, Quot.sound]`, no warnings or
`sorryAx`, stable direct guards and no monitor stop. Object SHA-256:
`5aaee0759cb98c0e1cafcc2c3a3d42c016b9f65c9827d8e584c46192c0226d34`.
The source comment “unchecked draft” predates this check; it is retained for
hash linkage. Transitive, dynamic and between-sample provider ancestry is
inherited, not rebuilt from source here.

This is a **conditional** bridge. The actual graph rank, its positive and
half-window bounds, and the strong and auxiliary norm hypotheses must still
be extracted and composed. No unconditional `m=R`, 72→76 reverse implication,
consistency equivalence, or iPRA endpoint is claimed.
