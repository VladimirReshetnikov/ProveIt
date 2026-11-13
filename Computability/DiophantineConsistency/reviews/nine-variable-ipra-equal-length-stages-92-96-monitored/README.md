# Equal-length nine-variable replay: stages 92–96 with resource sampling

The guarded equal-length-root verification replay completed
`ModelProgramLink`, `ModelBetaFunction`, `ModelRepArith`, `ModelRepInterfaces`
and `ModelRepFactorial`. The retained audit checks the entire prefix 1–96:
each author/verification output is byte-identical or becomes byte-identical
by replacing its single embedded source pathname with the same-length
verification pathname. Every differing direct-input hash must correspond
exactly to a previously checked predecessor. Direct and companion guards
match after mapping only those verified predecessor hashes and normalizing
overlay roots; sources and complete compiler logs match under source-path
normalization.

[`run.py`](run.py) starts guarded stages individually, checks `/proc/meminfo`
`MemAvailable` before each, and samples memory and Lean processes every two
seconds under the explicit two-Lean-process resource decision. Stages 92–95
had at most one Lean process in samples; five stage-96 samples show it
overlapping compact `ArithmeticControl215Table`. At most two Lean processes
were observed and the lowest sampled `MemAvailable` was 18,101,432 KiB.
[`check_overlap.py`](check_overlap.py) rechecks the recorded samples. Its
earlier stage-95-specific version and output are retained separately; that
earlier filter does not count the later compact module. These are sampled
observations, not continuous monitoring or a cgroup-limit proof.

[`audit.py`](audit.py) and [`capture.py`](capture.py) retain the full-prefix
comparison, sources, receipts, dependency listings and compiler logs under
[`observations`](observations/). The prior [1–91 prefix](../nine-variable-ipra-equal-length-stages-87-91-overlap/README.md)
is a separate frozen packet. These are sampled byte-level checks, not a proof
of Lean object-format semantics or a claim that all raw hashes match. Author
warning baselines and historical project/package/dynamic ancestry remain
inherited; the enumerator-based endpoint has not yet been reached in this
replay. Live `/tmp` overlays are needed to repeat the check.
