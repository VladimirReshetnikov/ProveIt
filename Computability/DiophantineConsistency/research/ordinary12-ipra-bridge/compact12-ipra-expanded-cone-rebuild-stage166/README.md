# Expanded compact/iPRA rebuild: stages 166–170

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `a255e5a7111d82cf83646551662dd85b88f44c2a69a4caa366cfed58e4e21ecb`.

Lean compiled stages 166–170 from the current DiophantineConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-034/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 170, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of seven samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,477,144 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `2a8d46e42b26377b39d03549a7da57fe8c882655d5e52a0969ec77ccdc4e0542`;
the observer SHA-256 is
`11ce47b431a8fe65741d3e36b5554d1167926fef4cc21c9130961303f74906d2`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 255 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
