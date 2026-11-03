# Expanded compact/iPRA rebuild: stages 186–190

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `bc0beedd944cbc7bc8936c805c4356f5cde029a7ad664ef61df9fc0e447879b5`.

Lean compiled stages 186–190 from the current BoundedZFCConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-038/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 190, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of seven samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,518,092 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `36adbaea83770a7d1036398eff6afd1772fe6f98a3306275bbaf172fecda03ef`;
the observer SHA-256 is
`97e0abfc9cd1a538d58d31af6d0cee9258e4e967984617b7cb4b56934826606e`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 235 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
