# Non-Q factor syntax weights: staged U retry

Outer session 93426 exited 1: the U proof reduced to a closed arithmetic goal
but did not close it; no object or postflight exists. The [independent
failure audit](../../reviews/current14-carrier65-other-weights-retry-failure-independent/)
passed. This retry changes only the U-weight proof. Instead of reducing the
whole large syntax tree by reflexivity, it uses the preceding V and S weight
equalities and a small explicit arithmetic expression. Limits and all theorem
statements remain unchanged. The no-Lean preflight and [independent prelaunch
review](../../reviews/current14-carrier65-other-weights-retry-prelaunch-independent/)
passed. The independently audited prior heartbeat
failure, missing object, and point-pinned providers are guarded.

The proposed results remain syntax weights only; actual field/evaluation and
polynomial degree bounds must be established separately.
