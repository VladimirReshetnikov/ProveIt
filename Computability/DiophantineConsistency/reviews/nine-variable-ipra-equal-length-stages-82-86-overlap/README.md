# Equal-length nine-variable replay: stages 82–86 with sampled overlap

The guarded equal-length-root verification replay completed `ModelScalarPR`,
`ModelOptimizer`, `ModelDirectScalar`, `ModelEnumeratorCantor` and
`ModelEnumeratorRows`. The retained audit checks the entire prefix 1–86:
each author/verification output is byte-identical or becomes byte-identical
by replacing its single embedded source pathname with the same-length
verification pathname. Every differing direct-input hash must correspond
exactly to a previously checked predecessor. Direct and companion guards
match after mapping only those verified predecessor hashes and normalizing
overlay roots; sources and complete compiler logs match under source-path
normalization.

These five stages overlapped the compact stage-95
`ArithmeticDagControlPerm222` retry under the explicit two-Lean-process
resource decision. [`run.py`](run.py) starts guarded stages individually,
checks `/proc/meminfo` `MemAvailable` before each and samples memory and Lean
processes every two seconds. Each stage has samples showing both processes;
at most two Lean processes were observed and the lowest sampled
`MemAvailable` was 17,384,252 KiB. [`check_overlap.py`](check_overlap.py)
rechecks the recorded samples. They are not continuous monitoring or a
cgroup-limit proof.

[`audit.py`](audit.py) and [`capture.py`](capture.py) retain the full-prefix
comparison, sources, receipts, dependency listings and compiler logs under
[`observations`](observations/). The prior [1–81 prefix](../nine-variable-ipra-equal-length-stages-77-81-overlap/README.md)
is a separate frozen packet. These are sampled byte-level checks, not a proof
of Lean object-format semantics or a claim that all raw hashes match. Author
warning baselines and historical project/package/dynamic ancestry remain
inherited; the enumerator-based endpoint has not yet been reached in this
replay. Live `/tmp` overlays are needed to repeat the check.
