# K tile-weight batch 00: physical witness rows 0–31

This bounded sixteen-stage source-only attempt replays the audited symbolic
provider, then proposes 32 separately named `decide +kernel` equalities for
actual Lean `selectorWeight (tile i)` at the candidate indices corresponding
to physical witness rows 0–31. The guard pins the independently reviewed
942-row witness, checks every proposed index/value against it, and records the
independently audited four-case feasibility sample. The sample is not reused
as a provider: every batch theorem is checked from the actual Lean definitions.

The physical row labels identify positions in an external candidate only;
this stage does not prove the actual ranks, remaining 910 weights, complete
coefficient array, K equality or file/gzip binding. No new theorem is claimed
until Lean and independent terminal review succeed. Resource limits retain
120 seconds per child, `-M3600`, 4-GiB sampled RSS and 10-GiB host floor;
the new source sets maxRecDepth 10000 and heartbeats 4000000, as in the
successful sample. Author no-Lean preflight exited 0. Runner SHA-256:
`18cbbe32075f847d147b488efd87adf353ea1212ba7f5bc00a1fc6dfefb1b823`;
manifest SHA-256:
`ccf104f03163938d2563cee4df50cb9e55ad7e72743d6a2baf1ccd31e8b1dd97`;
new source SHA-256:
`db8c0244e0c1b09423de19a7d2c3b051a41f797c14bcfcd607ba41103f48ba62`;
generator SHA-256:
`8a141e7dd6ea8e7818f9a059afae524b415a9b609d9e73e9edfeea8e0706f313`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-weight-batch00-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-weight-batch00-terminal-independent/README.md) passed; the packet is frozen.
