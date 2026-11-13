# Expanded compact/iPRA rebuild: stages 161–165

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `9a796815750b5c24d806faf1a30aaa95d8cd853e20204f4a888392c2e7f89ec6`.

Lean compiled stages 161–165 from the current DiophantineConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-033/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 165, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of seven samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,460,576 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `4d7c759af666ab11fa52748ee1d6e0f424ba39db06501932b604e0ef947947b7`;
the observer SHA-256 is
`1cfc48b9f3435ba6cb7788513de4b2ed2256a0a37a979a55c595cccd13d715e2`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 260 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
