# Independent source review: ordered-ring lower endpoint

Source SHA-256 `0bbf22dff40185310ea60c460befcc3b2729a59d7f49bb81e2d44dabb0d01c11`. The ring identity and stated inequality are mathematically valid; no Lean was run. The identity is the independently checked residual `c−k(Y+1)−slack=16X²Y⁴(X²+4X+4−2Y−W)` specialized to `2Y+W=X²+4X+4`. With X≥0,Y≥1,W≥0 every slack term is nonnegative and its constant 33 is positive, hence `k(Y+1)<c` in a linearly ordered commutative ring.

This is generic ordered-ring arithmetic and has no Pell, graph-zero, divisibility or model-cast binding. The `rw`/`linear_combination` elaboration, inferred ordered ring instances and whether `positivity` finds the Y−1 hypothesis remain to be checked by a guarded Lean run. The imported GuardFreeRankUpper provider and its closure must be selected and reconciled separately.
