# Expanded compact/iPRA rebuild: stages 141–145

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `5eb2e5bf63d3e738307f5bed0ec8f0af55b15a71f6085925ab812390243128f3`.

Lean compiled stages 141–145 from the current DiophantineConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-029/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 145, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of seven samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,515,460 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `5e1818b94aa765e914ddb0cdef39423934ab01b4e86d803b7b4fa24ceb406738`;
the observer SHA-256 is
`60b12ad8e5be9c0d2b6cecf18ff3283c3ba8c8afc6233155f3b148c7bd8b17dc`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 280 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
