# Conditional same-tuple `n=5,r=7` growth draft

This source is unchecked. It takes one positive model tuple, an explicit model bound `q≥2³⁰`, and explicit first-index-five and main-index-seven ordinate equations on that same tuple. It attempts to derive `65532·ι(b)·ι(Y)<ι(X)` using the audited generic growth theorem. The graph zero, index existence/alignment, and fixed-port lower bound are not assumed to follow from this source; later clients must supply them separately.

The source imports independently checked generic growth and the earlier seventh-ordinate identity, which transitively imports a fifth-ordinate identity. Their selected project and package providers must be reconciled, and the source/runner independently reviewed, before any coordinated Lean check.

The [independent source review](../../reviews/trace74-n5-r7-graph-growth-source-independent/README.md) checked the mathematical scope and same-tuple equations, not Lean elaboration. `selection.json` captures current first selections for the direct source imports and the y7 source's y5 import; the held runner rechecks these selections. Full serialized transitive/package and producer-time ancestry is not captured.

The [independent prelaunch review](../../reviews/trace74-n5-r7-graph-growth-prelaunch-independent/README.md) approved one coordinated check of the pinned runner and source.

Attempt01 actual tool session 2334 exited 1 and was reaped; the [terminal](observations/attempt01/terminal.json) SHA-256 is `1892e4a59a432aa85cac04f43bc5abec81731839d93930d3e6c220fdf6528965`. Lean reported missing `Trace74Pell` namespace and consequent unknown identifiers; no theorem was accepted. The import-only repair is held separately.
