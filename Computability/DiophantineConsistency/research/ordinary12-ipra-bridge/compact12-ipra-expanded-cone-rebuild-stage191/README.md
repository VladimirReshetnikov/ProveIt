# Expanded compact/iPRA rebuild: stages 191–195

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `8e191a7cb9cc003965e7c2008e6ca18f919af9dae06873ccb8451c666bff4ef8`.

Lean compiled stages 191–195 from the current BoundedZFCConsistency and
BusyBeaver source trees in pinned selected-object topological order; each
exited 0 without warnings or `sorryAx` within the 180-second per-stage cap.
Source snapshots, direct dependencies, guards, logs, hashes and receipts are
under `observations/batch-039/`. The wrapper rechecked the full selected
overlay, source hashes, outputs, warning baselines and direct guards and exited
0 with `completed: 195, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of six samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,602,092 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `3df813e27d7f9b5e1ac99344a509c78888b2b3aa3eb399a2ddd6a948963b75af`;
the observer SHA-256 is
`b3fe67e4897d5c83ca81d0ff6ab92f111dd6cfc96ef8f119647cdacff058f915`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 230 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
