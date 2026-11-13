# Artifact audit: first two nine-variable author stages

The fresh `h` overlay has two recorded successful stages:
`WeightedExpressionDegree` and `ModelDifferenceRing`. This packet retains
their receipts, direct-dependency outputs, complete compiler logs and the
registered warning policy; the live `.olean` objects remain in `/tmp`. The
subsequent stages and both nine-variable endpoints are outside this audit.

[`audit.py`](audit.py) checks retained against live receipts and logs, the
current and frozen source hashes, the two output objects and their published
hard links, and all 120 and 160 recorded direct-candidate guards. It checks
direct dependency precedence and companion coverage, the warning-policy
guards, and the pinned standard-QM40 and native-parent guards at sampled
boundaries. The second compiler output has exactly the same **complete**
11-warning text as the earlier rejected observation after replacing only the
source path; its source hash matches the registered policy. The earlier
warning-bearing object was not published. The normal audit exited 0 and
optimized Python was rejected.

The earlier rejected and later accepted `ModelDifferenceRing` objects have
different hashes. The earlier failure did not retain direct-input hash guards,
so these observations do not determine the cause and should not be treated as
a reproducibility match. The accepted run has its own direct guards; neither
run authenticates transitive, package or dynamic-loading ancestry or excludes
between-check changes. This is a point-in-time single-author artifact audit,
not an independent Lean replay. The original `/tmp` artifacts are required to
repeat the live checks.

The reviewer's first audit invocation used a mistyped runner hash and failed;
after correcting it to the measured manifest value, the checks passed. That
failure was in the audit script, not a Lean compiler or proof failure.
