# Expanded compact/iPRA rebuild: stages 136–140

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `22349e4165491b9861c8135761d3859ee3b17735ba73c8433071642c54f62a22`.

Lean compiled stages 136–140 from the current FirstOrder, PAHF and
DiophantineConsistency source trees in pinned selected-object topological
order; each exited 0 without warnings or `sorryAx` within the 180-second
per-stage cap. Source snapshots, direct dependencies, guards, logs, hashes
and receipts are under `observations/batch-028/`. The wrapper rechecked the
full selected overlay, source hashes, outputs, warning baselines and direct
guards and exited 0 with `completed: 140, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of eleven samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,458,308 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `26bfc927984d5fe17ab3019896bece94fe4e324483712ca3aedb2c625b61c0b1`;
the observer SHA-256 is
`514579197f7554f24ad86bbec85b356024f70c1233328e6eb952e983873fdffa`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 285 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
