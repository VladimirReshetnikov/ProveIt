# Expanded compact/iPRA rebuild: stages 203–207

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the four
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `19210479c7951ab61b08f861bbff275ea2f70a2e197becc0e1bac021a76c52cd`.

Lean compiled stages 203–207 from the current BusyBeaver source tree in pinned
selected-object topological order; each exited 0 without warnings or `sorryAx`
within the 180-second per-stage cap. Source snapshots, direct dependencies,
guards, logs, hashes and receipts are under `observations/batch-041/` and
`observations/batch-042/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 207, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of six samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,610,024 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `c110d35c323ac56327990fe5263b488f42c80bba04d4dfad085d9eac5ad5e3d7`;
the observer SHA-256 is
`436d5a6458d11a9b2756735e0269dbbb93b02ae93dd385f6ba6cf4297dc88fc0`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 218 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
