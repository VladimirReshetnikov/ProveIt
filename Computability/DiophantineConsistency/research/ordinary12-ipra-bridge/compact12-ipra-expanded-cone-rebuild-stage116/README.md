# Expanded compact/iPRA rebuild: stages 116–120

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `da39b0f0479e2b6ee60e43550f17e163bdc87b5f47c925fbd1180c1db0a6721f`.

Lean compiled stages 116–120 from the current DiophantineConsistency and
BusyBeaver source trees in pinned selected-object topological order; each
exited 0 without warnings or `sorryAx` within the 180-second per-stage cap.
Source snapshots, direct dependencies, guards, logs, hashes and receipts are
under `observations/batch-024/`. The wrapper rechecked the full selected
overlay, source hashes, outputs, warning baselines and direct guards and exited
0 with `completed: 120, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of nineteen samples showed more than one Lean process, and
minimum sampled MemAvailable was 17,616,816 KiB. Exact PIDs, arguments, RSS
and timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `89a4d533a7865e63453c283a718f3603ab145f1d600da495d342f5853c6f9f87`;
the observer SHA-256 is
`97896481297984981544e21a7440914f5fbe9aeed77f5d359306976a9088b2ed`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 305 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
