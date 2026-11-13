# Expanded compact/iPRA rebuild: stages 96–100

This bounded author batch resumed the corrected 425-module merged-root build
after the separately guarded successful stage95 retry. It revalidated the
original stage95 timeout receipt and its unchanged dependencies, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, all earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it also required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `d8bc7c3f981595528b92f175cedeccdad402dec3b1b6849a1d64c554bf047b5e`.

Lean compiled stages 96–100 in the pinned selected-object topological order;
each exited 0 without warnings or `sorryAx` within the 180-second per-stage
cap. Stage96 took 137.676 seconds, stage97 took 66.536 seconds, and stage98
took 25.962 seconds. Source snapshots, direct dependencies, guards, logs,
hashes and receipts are under `observations/batch-020/`. The wrapper then
rechecked the full selected overlay, source hashes, outputs, warning baselines
and direct guards and exited 0 with `completed: 100, total: 425`.

The separately monitored equal-length peer ran in another output root under
the coordinator's two-Lean-process allowance. `observe_run.py` sampled all
Lean processes and available memory every five seconds: 31 of 52 samples
showed two Lean processes, none showed more than two, and the minimum sampled
MemAvailable was 17,969,012 KiB. The exact PIDs, arguments, RSS and timestamps
are in `observations/execution-monitor/monitor.json`. Sampling cannot exclude
shorter overlaps or memory dips between checks. The monitor SHA-256 is
`843486cbb8cc4334fce408a616e86e29b3235e7827e0593cb6e76fc288c07f09`;
the observer SHA-256 is
`b6a6445990870773bdc4b24b8d6b543ed072625e1e4f1f870983840f9082e166`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 325 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
