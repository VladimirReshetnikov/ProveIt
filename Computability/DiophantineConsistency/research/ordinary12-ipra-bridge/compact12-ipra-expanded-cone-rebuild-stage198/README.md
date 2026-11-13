# Expanded compact/iPRA rebuild: stages 198–202

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the four
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `5e1d52e715eab8436a192b01d7ea3c790b99050510cdf70d1f6a34bc0fbce258`.

Lean compiled stages 198–202 from the current BusyBeaver source tree in pinned
selected-object topological order; each exited 0 without warnings or `sorryAx`
within the 180-second per-stage cap. Source snapshots, direct dependencies,
guards, logs, hashes and receipts are under `observations/batch-040/` and
`observations/batch-041/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 202, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of six samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,587,716 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `cd117196468650d2db0786b97ce16af966ab3708fd57f7438815e392612c4661`;
the observer SHA-256 is
`ee2edb83aaa58d219266790023adc3ae5fa356018f8e84d9235918a89a17851a`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 223 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
