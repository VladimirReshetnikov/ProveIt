# Generic three-block finite partition probe

This source-only one-stage diagnostic proposes a generic `Fin.addCases`
partition of an arbitrary predicate over `Fin 9` into blocks of sizes 2, 3
and 4, using the same nested `natAdd`/`castAdd` shape planned for global
candidate chunks. It imports the audited Fin942 provider only as the
established checked environment. It does not prove any candidate fact,
global order, physical rank, K or file binding. Corrected Init route,
one-thread and per-child guards are retained. Author no-Lean preflight
exited 0.

Runner SHA-256:
`c1aefefebaaaef4108a46cf4d47f5fab079e3660d5af97e322290be97b82bbde`;
manifest SHA-256:
`4bdfe3f5d5cb345e83abe7593a408df4e88b302d5ad0d8b50f1ad631d7f85283`;
source SHA-256:
`7d368f98e776966099943ccc63a291a9d617821344aa5722c2c1c6c098ceb601`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-partition-probe-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-k-partition-probe-terminal-independent/README.md) passed; the packet is frozen.
