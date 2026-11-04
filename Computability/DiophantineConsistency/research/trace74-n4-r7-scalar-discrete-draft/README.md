# `n=4, r=7` scalar endpoint join draft

This is unchecked source. It assumes a discrete ordered ring, `q≥32`, `x≥32`, `Y≥1`, the same witnesses `x=q*w` and `Y=q³*s`, and explicit strict comparisons between the listed scalar polynomials `ky`, `c`, and `k`. It applies separate lower/upper endpoint providers and derives a positive multiple of `q` below `q`, a contradiction. It asserts no graph-zero, Pell-ordinate, fixed-port, or iPRA result.

The two imports and their selected provider closures must be reconciled; source and prelaunch review plus root slot sequencing are required before Lean. The endpoint providers themselves are still under author check or review.

The [independent source review](../../reviews/trace74-n4-r7-scalar-discrete-source-independent/README.md) checked the conditional mathematics and witness linkage; it does not establish Lean acceptance or provider compatibility.

The [independent prelaunch audit](../../reviews/trace74-n4-r7-scalar-discrete-prelaunch-independent/README.md) approved one coordinated run. `selection.json` captures current first selections for direct endpoint-source imports and `run.py` rechecks that capture; no full transitive/package or producer-time ancestry capture is claimed.

One author run completed in actual tool session 44001, exit 0 and fully reaped. Its [terminal](observations/attempt01/terminal.json) SHA-256 is `f825f98389d0a0f17e180a4f765608f2db01de07209744402c708f1c2309e951`, and the object `/tmp/trace74-n4-r7-scalar-join-7wa985vx/lib/Trace74N4R7ScalarDiscrete.olean` has SHA-256 `2e1c3e4e33767611fc02997d6ea7fcf76d795333187232b202607612ac95100e`. The [independent result audit](../../reviews/trace74-n4-r7-scalar-discrete-result-independent/README.md) passed. The theorem remains conditional and has no graph binding.
