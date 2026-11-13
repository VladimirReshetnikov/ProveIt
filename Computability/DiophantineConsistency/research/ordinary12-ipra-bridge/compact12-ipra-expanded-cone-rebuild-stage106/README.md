# Expanded compact/iPRA rebuild: stages 106–110

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `442bea0843ed614166bc00e9ae8daf95930022e763764fb48ceeae2ed5a1fcaf`.

Lean compiled stages 106–110 from the current DiophantineConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-022/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 110, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of the ten samples showed more than one Lean process, and
minimum sampled MemAvailable was 18,430,864 KiB. Exact PIDs, arguments, RSS
and timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `aef8e1c94c27cd09e7dc715c4b4e6a7dd18e7607de9d29c46fa8afdcc783e6d6`;
the observer SHA-256 is
`1163973453e84df92a854a41838c6efdb39ab22342f52fb227c7e7e00e94fa21`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 315 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
