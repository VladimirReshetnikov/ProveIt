# Expanded compact/iPRA rebuild: stages 151–155

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `b3f7a80f3dab1a4b724564ce2a24876178bffa658db323a9e6f2d28e981b051d`.

Lean compiled stages 151–155 from the current DiophantineConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-031/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 155, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of six samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,472,576 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `0c49a382ca3bcb39a822d30e6918c8ceeb66db509c36914f5218b344739891d7`;
the observer SHA-256 is
`8c4a2037bd01a5e85f2d27f9ad70500357df9eaa3d3c54642b272130b527e3fc`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 270 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
