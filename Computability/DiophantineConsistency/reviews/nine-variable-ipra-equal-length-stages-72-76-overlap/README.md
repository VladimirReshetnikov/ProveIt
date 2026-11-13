# Equal-length nine-variable replay: stages 72–76 with sampled overlap

The guarded equal-length-root verification replay completed `ShortCircuit`,
`ConsecutivePell`, `TotalDegreeBound`, `ShortSystem` and `Carrier65`. The
retained audit checks the entire prefix 1–76: each author/verification
output is byte-identical or becomes byte-identical by replacing its single
embedded source pathname with the same-length verification pathname. Any
differing direct-input hash must correspond exactly to a previously checked
predecessor. Direct and companion guard records match after mapping only
those verified predecessor hashes and normalizing overlay roots; sources and
complete compiler logs match under source-path normalization.

These five stages ran concurrently with the compact stage-95
`ArithmeticDagControlPerm222` retry, following the explicit two-Lean-process
resource decision. [`run.py`](run.py) started one guarded stage at a time,
required at least 8 GiB of `/proc/meminfo` `MemAvailable` before starting,
and sampled memory and Lean processes every two seconds. Each stage has
samples showing both processes. The maximum observed was two Lean processes;
the lowest observed `MemAvailable` was 17,669,212 KiB. These are sampled
observations, not continuous process/memory monitoring or a cgroup-limit
proof. [`check_overlap.py`](check_overlap.py) rechecks the retained samples.

[`audit.py`](audit.py) and [`capture.py`](capture.py) retain the full-prefix
comparison, source snapshots, receipts, dependency listings and compiler
logs under [`observations`](observations/). The prior [1–71 prefix](../nine-variable-ipra-equal-length-stages-67-71/README.md)
is a separate frozen packet. The comparison is byte-level evidence, not a
proof of Lean object-format semantics or a claim that all raw hashes match.
Author warning baselines and historical project, package and dynamic ancestry
remain inherited; neither endpoint has been reached in this replay. Live
`/tmp` overlays are needed to repeat the prefix check.
