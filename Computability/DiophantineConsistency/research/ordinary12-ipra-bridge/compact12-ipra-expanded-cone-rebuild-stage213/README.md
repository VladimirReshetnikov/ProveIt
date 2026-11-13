# Expanded compact/iPRA rebuild: stages 213–217

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the four
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `2e70e69c8ab50c7981bcd63c990337173781b8e583b1ada572c94f5267f72463`.

Lean compiled stages 213–217 from the current BusyBeaver source tree in pinned
selected-object topological order; each exited 0 without warnings or `sorryAx`
within the 180-second per-stage cap. Source snapshots, direct dependencies,
guards, logs, hashes and receipts are under `observations/batch-043/` and
`observations/batch-044/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 217, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of five samples captured a Lean process, although all five brief
Lean children ran and returned 0. Minimum sampled MemAvailable was 18,469,036
KiB. Exact PIDs, arguments, RSS and timestamps are in
`observations/execution-monitor/monitor.json`. Sampling cannot exclude shorter
overlaps or memory dips between checks. The monitor SHA-256 is
`5085a44d981bdf6e44da56f854e29c84e08509e2442cfe0e02d873a18982b29d`;
the observer SHA-256 is
`9c572161e2aefd69e2a2f58639e0f165a0b71f4d63cd1daf1126f54c1055451f`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 208 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
