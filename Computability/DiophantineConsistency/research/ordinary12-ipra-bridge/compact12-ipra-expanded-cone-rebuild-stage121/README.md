# Expanded compact/iPRA rebuild: stages 121–125

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `a97de1ec2aa770cede25f2c4cf73a223214c82a4e82a6541298507bfc87212bd`.

Lean compiled stages 121–125 from the current DiophantineConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-025/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 125, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of fourteen samples showed more than one Lean process, and
minimum sampled MemAvailable was 18,397,036 KiB. Exact PIDs, arguments, RSS
and timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `5ac0f8e4bdff71fe8cbe257822a25ae3f62fbcacb798f2e08308c36c73a36421`;
the observer SHA-256 is
`72557e60dafe8a68eb00bac72b48653d0afa83415003d4d0ac40e9b6f7e08994`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 300 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
