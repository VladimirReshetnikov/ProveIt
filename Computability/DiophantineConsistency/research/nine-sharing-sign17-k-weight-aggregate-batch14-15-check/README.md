# K tile-weight aggregate batches 14–15: witness rows 864–941

This bounded 17-stage source-only attempt replays the audited symbolic
provider and proposes a `Fin 64` equality for rows 864–927 and a `Fin 14`
equality for rows 928–941, relating actual Lean tile weights to candidate
index/weight vectors from the pinned external witness. The final vector and
the runner's vector-pattern guard use length 14. Witness row labels are
candidate positions, not established physical ranks. Other rows, rank
ordering, complete K, and external file/gzip binding remain separate. The
same per-child resource guards apply. Author no-Lean preflight exited 0.

Runner SHA-256:
`117846d0290f335a99a8f1881d35c421802204c73ed2ddd10a3c28d66646b615`;
manifest SHA-256:
`bf275bee675805f96ecd1181a24015d2f613509e6eb8b3a726b639d34f05185f`.
Sources for batches 14 and 15 have respective SHA-256:
`0ca4d1ebff9b77f75072616f097fd8b516129ef5d7c8de167e8872804b765f03` and
`3bdac559fb0c20604a33cc872e1c69e2e2934e7f1d9f0f770abc7cbf3a11654b`.
Generator hashes are respectively
`051d2f554aa0bc94e36ca14099a53c26dd3119277c2a6f4b520e221c421e0008` and
`e9ad12e5d7d4343bda214edcc01054c47212c695d9eff0082309f87b857a43e9`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-weight-aggregate-batch14-15-prelaunch-independent/README.md) passed. The final generator retains a stale docstring saying 64 rows; its executed slice, emitted vector, and result metadata use 14.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-weight-aggregate-batch14-15-terminal-independent/README.md) passed; the packet is frozen.
