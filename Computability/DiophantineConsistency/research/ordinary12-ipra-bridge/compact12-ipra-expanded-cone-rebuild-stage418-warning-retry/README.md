# Expanded compact/iPRA rebuild: stage 418 exact-warning retry

The rejected attempt emitted four unused section-variable warnings and two
unused simp argument warnings. This retry keeps the source unchanged and
accepts only the complete, source-pinned warning log after path normalization.
Five mutation checks reject added, missing and altered warnings, an added
error and an added `sorryAx`. This exception is not a proof audit.

The runner rechecked all 425 source pins, selected overlay, earlier receipts
and warning baselines, and rejected direct dependency guards. It quarantined
the rejected object and rebuilt the unchanged source. Lean exited 0 in 8.458
seconds; the exact warning verifier and final guards passed at 418/425, with
source and direct dependencies unchanged. Retry and quarantined object
SHA-256s both equal
`0ecb5fef2a0fc52138b9c21e02170118d091995d17b417bcb0af19fe61464145`.

Source, rejected log, normalized baseline, verifier and runner SHA-256s are
respectively `2bdd4d88873db9d834b03e14cfc2596ce85cc75eab44734716a60d4092b5bd51`,
`712c6ca9127aff8879724232a5d9492bc1b7c4fbc621b3c15a4252dbfdb591bf`,
`685b3a91d1170abd6b5cc38ed93b59402d0d6e69265f776b5ec318f6183db0ef`,
`2598551bc57f922ea29ada75cb086429da5bc003b4a6d78c50dc338d8b007416`, and
`8ee03e05e39152e0fc78a5c72f82f1ef3c0a73733d2bd489f2a12e5f079495dc`.
Raw observations, mutation results and quarantine receipt are retained.

Five-second monitoring sampled at most one Lean child and minimum available
memory 18,418,724 KiB; brief children or overlap can be missed. This author
prefix is not an iPRA endpoint, independent replay, or full provider audit.
Seven stages and the compact model-to-iPRA join remain; package and dynamic
ancestry are not authenticated. Stage 419 may encounter the known newer-helper
source/provider mismatch.
