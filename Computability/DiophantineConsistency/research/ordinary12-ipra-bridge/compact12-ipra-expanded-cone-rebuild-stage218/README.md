# Expanded compact/iPRA rebuild: stages 218–222

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the four
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `3a50252e01ca6007940d245cfa1610aba016e493ae76ff6cc9aed1d5f03bb98b`.

Lean compiled stages 218–222 from the current BusyBeaver source tree in pinned
selected-object topological order; each exited 0 without warnings or `sorryAx`
within the 180-second per-stage cap. Source snapshots, direct dependencies,
guards, logs, hashes and receipts are under `observations/batch-044/` and
`observations/batch-045/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 222, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of seven samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,411,964 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `6e90361bcd513eab7e84f437328e9cae0f6be5d5d779ac212495f634fdcaf7ce`;
the observer SHA-256 is
`c49c3fe6bf988ca4ee7f33c2c3bce614a2b9227447cd56ab4205e3591d290309`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 203 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
