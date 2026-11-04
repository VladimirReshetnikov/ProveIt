# Fixed symbolic beta gives a large q: source draft

This source is unchecked. It takes `p 0=betaNat` and `v 0>0`, and attempts to prove the same tuple's `q≥2³⁰`. It uses `betaNat+1=Exp.exp(67·8807)`, monotonicity at exponent 30, and `v 0≥1`; only `2³⁰` is normalized. The huge fixed beta is locally irreducible.

No graph-zero or index statement is asserted. Imports and first-selected provider ancestry require reconciliation, and source/prelaunch review and root slot sequencing are required before a Lean check.

The [source review](../../reviews/trace74-fixed-q-large-source-independent/README.md) and [prelaunch review](../../reviews/trace74-fixed-q-large-prelaunch-independent/README.md) passed. One author run completed in actual session 86027, exit 1/reaped; its [terminal](observations/attempt01/terminal.json) SHA-256 is `e38c7b5199b6b370e1f8a85120cf62714c35ad127dc76f314c5c9758abaadc7d`. Lean reported an addition-orientation mismatch and an extra tactic after a solved goal, followed by `sorryAx`; the stage is rejected. A separate two-line proof repair is under review.
