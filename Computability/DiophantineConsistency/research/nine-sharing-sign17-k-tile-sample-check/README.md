# K ranking: four actual Lean tile-weight feasibility samples

This nineteen-stage source-only attempt replays the audited symbolic provider,
then separately asks Lean to check four sample weight equalities against the
actual `WangTiles942.tile` and `selectorWeight` definitions: Start (index 0),
a high-index tail row (926), one transition row (126) and one copy row (432).
Each candidate index/value is externally pinned to the independently reviewed
[942-row witness](../nine-sharing-sign17-k-ranking-witness/README.md). Each
sample is isolated in its own module to identify failure/resource cost.

This is a finite feasibility probe, not a proof of the other 938 rows, the
physical permutation, the coefficient array, K, or any external file/gzip
binding. The witness-to-source check is Python provenance. The provider and
resource guards are retained. Author no-Lean preflight exited 0. Runner
SHA-256:
`0e62fb5f10b3aaa3e348e9de72a6bd51fbe78b9cf51d7881c708068826e7c708`;
manifest SHA-256:
`d29a7cd487419fb002691cdc585554e892d00246211f4ec06019e59f81467504`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-tile-sample-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-tile-sample-terminal-independent/README.md) passed; the packet is frozen.
