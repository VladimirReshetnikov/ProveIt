# Ordered-ring scalar growth source draft

`Trace74N4R5ScalarGrowth.lean` is an **unchecked** attempt at the three conditional ordered-ring inequalities in the separately audited [scalar certificate](../trace74-n4-r5-scalar-growth/README.md). It assumes the polynomial strict inequality `kY<c` explicitly; its size bound additionally assumes `q≥32` and `Y≥q³`. Neither this source nor the arithmetic certificate binds those assumptions to an actual graph zero. No Lean run or theorem acceptance is claimed.

The intended later graph proof must separately supply the same `X,Y,q`, the Pell ordinate identity, the strict inequality, and the weighted projection divisibility. The draft imports Mathlib ordered-ring and tactic infrastructure directly; provider ancestry and direct selections must be recorded before any author check.

Independent source review: [ordered-ring source audit](../../reviews/trace74-n4-r5-scalar-growth-source-independent/README.md) (PASS). It checks the mathematical argument, not Lean elaboration. `run.py` is held for separate prelaunch review and slot coordination; the `prelaunch/` receipt records a read-only pin check and report-policy controls.

The [independent prelaunch review](../../reviews/trace74-n4-r5-scalar-growth-prelaunch-independent/README.md) approved the corrected runner. Its `prelaunch-v2/` receipt includes the corrected search-path check; the earlier receipt is retained alongside the finding that its runner could not launch.

Attempt01 was run once; actual tool session 89070 exited 1 and was reaped. [The retained terminal](observations/attempt01/terminal.json) has SHA-256 `62441b2b4bd703d15430deb77d6f6bd85589818dade7c7d4b18cfbc23b6b3a20`. Lean reported a missing `MulRightStrictMono R` instance at the final cancellation in `x_gt_four_y_cube`; its printed `sorryAx` is a consequence of that error. The full stage is rejected. A separate source-only retry is under review.

Independent [factual and repair-source review](../../reviews/trace74-n4-r5-scalar-growth-repair-source-independent/README.md) confirms the failure and unchanged theorem statements; it does not accept a Lean theorem from the failed attempt.
