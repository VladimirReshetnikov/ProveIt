# Expanded compact/iPRA rebuild: stages 156–160

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `846026a513dc994527beb78ea81962a6c1011802a8d454385fdc1c68a2e350eb`.

Lean compiled stages 156–160 from the current DiophantineConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-032/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 160, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of eight samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,576,312 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `450cd6a1ee613bf78d16ce6b33b4a7c2d42c8a161baf194c1b134c2058385c3b`;
the observer SHA-256 is
`4fc3f65eca047649534236214955cc1c02f661a2438414188c8bc841effb57f3`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 265 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
