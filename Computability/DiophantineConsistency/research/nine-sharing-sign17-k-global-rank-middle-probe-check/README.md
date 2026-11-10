# Middle global candidate nonzero and adjacency cases

This checked one-stage diagnostic imports the audited Fin942 provider and
pins the successful first-16-case probe and audit. It proves 64
global nonzero cases and 64 global numeric adjacency cases at offset 448,
crossing an original block boundary, directly on the nested Fin942 vectors.
The `Fin.natAdd`/`castAdd` offsets are chosen to support later bounded
partitioning. This is only a scale/definitional-reduction test, not a global
order, rank, K or file theorem. Corrected Init, one-thread and per-child
resource guards are retained. Author no-Lean preflight exited 0.

Runner SHA-256:
`4117697368e3cdde91820f1d2f47c3f070db25546d2aa9bd015cfd8c5603ccd5`;
manifest SHA-256:
`d6d287e1eb4df3112115fe6cee760ee32c2e16463954369739acf4b877f64c1c`;
source SHA-256:
`a4d81f1baa4445460ae26705cd0304da089407c96f9ecdadb750d317e6304244`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-global-rank-middle-probe-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-global-rank-middle-probe-terminal-independent/README.md) passed; the packet is frozen.
