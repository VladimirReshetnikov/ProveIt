# Expanded compact/iPRA rebuild: stages 111–115

This bounded author batch resumed the corrected 425-module merged-root build.
It revalidated the earlier stage95 timeout and successful retry, all prior
runner hashes, baselines and quarantines, the 425 source pins, selected
original and merged provider files, earlier output/log hashes, the three
source-pinned exact-warning verifiers, and earlier direct dependency and
companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The exact runner
SHA-256 is `4c88c9d352d251478ba007c483767bd06ca9f9d6a6b1f444030d992f778e5e94`.

Lean compiled stages 111–115 from the current DiophantineConsistency and
BusyBeaver source trees in pinned selected-object topological order; each
exited 0 without warnings or `sorryAx` within the 180-second per-stage cap.
Source snapshots, direct dependencies, guards, logs, hashes and receipts are
under `observations/batch-023/`. The wrapper rechecked the full selected
overlay, source hashes, outputs, warning baselines and direct guards and exited
0 with `completed: 115, total: 425`.

`observe_run.py` sampled Lean processes and available memory every five
seconds: none of eleven samples showed more than one Lean process, and minimum
sampled MemAvailable was 18,224,256 KiB. Exact PIDs, arguments, RSS and
timestamps are in `observations/execution-monitor/monitor.json`. Sampling
cannot exclude shorter overlaps or memory dips between checks. The monitor
SHA-256 is `02cb3430d555f7cbf492fed07c8d26f55b8e5b218afd77ce73f2808b31351b13`;
the observer SHA-256 is
`0f03a7148b603d396251a258b2523da3236fc56650134a4f61906bbf2d6331f2`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source/object import-shape agreement does not authenticate the
historical origin of inherited objects. Package, dynamic and broader provider
ancestry remain unverified; 310 rebuild stages and the compact model-to-iPRA
join remain open. File/resource guards are point-in-time.
