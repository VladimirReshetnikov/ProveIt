# K Start and initial non-Start ordering sample

This checked 17-stage attempt replays the independently audited Fin32
weight probe for candidate rows 0–31, then proves that row 0 is
the Start index, rows 1–31 are nonzero, and the 30 adjacent weight
comparisons between rows 1–31 hold numerically and for actual Lean tile
weights. It correctly excludes the Start row from descending-weight order.
The boundary to row 32, remaining blocks, actual candidate ranks, full K and
file binding remain separate. Usual per-child guards apply. Author no-Lean
preflight exited 0.

Runner SHA-256:
`e41dfa7f7224fb13aea1b14c39a159b90206726af7ffe1f7577aac7847056d77`;
manifest SHA-256:
`31a8789f4f6b63039c5b29779dfe3eb66f397ce4a669105beac9a3f0c53c45f7`;
source SHA-256:
`77b48e6a3bf74fe34c4f12a6ed73aebc9ce0425e42f246a1b749b57d27ae7dc2`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-order-probe-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-order-probe-terminal-independent/README.md) passed; the packet is frozen.
