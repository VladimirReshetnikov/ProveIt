# Expanded compact/iPRA rebuild: stages 146–150

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `583e05f9d4ddea607df3f3b429ee3fd2b39cfa2743ad5639cbe9f66296ab72cb`.

Lean compiled stages 146–150 from the current DiophantineConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-030/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 150, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of five samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,561,424 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `cb48481b2040e2ac04477acf5a8c26895caf142f6445ce079951f2ff8183af1c`;
the observer SHA-256 is
`82c3560e7fc14c2fc3ade2409daeb5966c8a534db9a7b6466f8edf9620b41efc`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 275 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
