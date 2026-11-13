# Expanded compact/iPRA rebuild: stages 208–212

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the four
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `fd52d98b6e6daee71d9b769a278bdc8d509359ab7aa0dbdd05c7a8558bd0ba68`.

Lean compiled stages 208–212 from the current BusyBeaver source tree in pinned
selected-object topological order; each exited 0 without warnings or `sorryAx`
within the 180-second per-stage cap. Source snapshots, direct dependencies,
guards, logs, hashes and receipts are under `observations/batch-042/` and
`observations/batch-043/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 212, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of five samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,561,020 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `254443f6fbb7bd3e184e5a1e016fa0bb996405989d6ac5d3434887b0f831afb1`;
the observer SHA-256 is
`26a831fcf8f4407a8bfbd4697fb38445ad2565f8922e163d5b648adabcf9ab54`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 213 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
