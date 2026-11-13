# Expanded compact/iPRA rebuild: stages 126–130

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `60a6d42394910d3ce5e3430d6d806464b7a9be050ff374b0ca5e1d399b6b994d`.

Lean compiled stages 126–130 from the current DiophantineConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-026/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 130, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of eleven samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,453,664 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `8f817b0222af213497f525fdd5437ef175c1b66d37a4342ab06f5a672a2c9518`;
the observer SHA-256 is
`c8f965ec77dca001605278a9b789f758128b6b15c56b4338ee6dd812c0d3a16e`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 295 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
