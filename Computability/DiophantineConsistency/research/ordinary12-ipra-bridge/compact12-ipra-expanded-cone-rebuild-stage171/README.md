# Expanded compact/iPRA rebuild: stages 171–175

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `f9cd1aca4fa7b13bc7376f1441102f9aec8f0b2ec5a912e5a5102f6690cafd7b`.

Lean compiled stages 171–175 from the current DiophantineConsistency and ZF
source trees in pinned selected-object topological order; each exited 0
without warnings or `sorryAx` within the 180-second per-stage cap. Source
snapshots, direct dependencies, guards, logs, hashes and receipts are under
`observations/batch-035/`. The wrapper rechecked the full selected overlay,
source hashes, outputs, warning baselines and direct guards and exited 0 with
`completed: 175, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of nine samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,411,684 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `7cb1fd527f76ce88b6285e690caf288e72e4946480cec1f66aeba696d52e6629`;
the observer SHA-256 is
`7830686fbb74166f225362cb961484eab91e53b8689dd6e13713b0ad37b1b678`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 250 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
