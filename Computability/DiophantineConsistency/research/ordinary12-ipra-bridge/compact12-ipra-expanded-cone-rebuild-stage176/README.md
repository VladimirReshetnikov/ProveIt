# Expanded compact/iPRA rebuild: stages 176–180

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `07f9149536f2ee41eecd9d215c55b2a224098bde0bfbcfbd787972040cccf173`.

Lean compiled stages 176–180 from the current BoundedZFCConsistency source
tree in pinned selected-object topological order; each exited 0 without
warnings or `sorryAx` within the 180-second per-stage cap. Source snapshots,
direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-036/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 180, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of six samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,562,152 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `5cdd4e9b109e8b66ef49f651ec9db7a3f4a3f6d1ffb7050de1869f24671b7889`;
the observer SHA-256 is
`b6e2720e5a6ed158b86d3638e5e1ff76e2aa3daac7eea7f987f0d94bc091c002`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 245 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
