# Expanded compact/iPRA rebuild: stages 131–135

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `e9e61e7e89f956025ac09573a2e4cbf88a0c949ffe7a29a68a4911cf5a7d2737`.

Lean compiled stages 131–135 from the current DiophantineConsistency,
BusyBeaver and FirstOrder source trees in pinned selected-object topological
order; each exited 0 without warnings or `sorryAx` within the 180-second
per-stage cap. Source snapshots, direct dependencies, guards, logs, hashes
and receipts are under `observations/batch-027/`. The wrapper rechecked the
full selected overlay, source hashes, outputs, warning baselines and direct
guards and exited 0 with `completed: 135, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of five samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,641,896 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `616ad61340f77f6a951ec82b414fcd15ae0ddd841f25ce3a4589b62a1a0ee390`;
the observer SHA-256 is
`eb8fbf7abf5c8d04a7bc08ecebc0d8cd0920a5f8b1542184bd87f00b87630784`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 290 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
