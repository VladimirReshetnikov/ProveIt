# Ranked K rawWord split: sentinel-reduction retry

This checked one-stage retry retains the failed client's statements and
provider/resource guards. Its only source change adds three `rfl` facts and
scoped simplification for the previously unreduced sentinel-vector values. The runner
enforces that exact delta and pins the failure receipt and audit. Even a
successful rawWord split leaves collision aggregation and external
coefficient/file binding separate. Author no-Lean preflight exited 0.

Runner SHA-256:
`b43b9ae175f9056316616e6f8c78790a6a9a183b8c79fb2e0e7e65788ae49ba3`;
manifest SHA-256:
`f02853edc208faf626f6934722df7bbc86a487a3db76006fba486b47b95d4890`;
source SHA-256:
`dc3b1a8150c32892c35b5574da3e5fa71e329a6c5cc374eb7afebcfe11499bea`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-ranked-rawword-retry-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-ranked-rawword-retry-terminal-independent/README.md) passed; the packet is frozen.
