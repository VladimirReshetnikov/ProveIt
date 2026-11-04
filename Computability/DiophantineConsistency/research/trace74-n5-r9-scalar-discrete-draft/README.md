# `n=5,r=9` discrete scalar join draft

Unchecked source, based on the independently audited [scalar arithmetic](../trace74-n5-r9-scalar-obstruction/README.md). It assumes a discrete ordered ring, same `q,x,Y`, `q≥73`, `x≥32`, `Y≥1`, divisibility witnesses `x=q*w` and `Y=q³*s`, and strict scalar interval inequalities. It uses the lower/upper endpoint providers to contradict a positive multiple of `q` below `q`.

Both endpoint providers have independently audited Lean checks. No graph-zero, fixed-port or iPRA conclusion is asserted.

The [independent source review](../../reviews/trace74-n5-r9-scalar-discrete-source-independent/README.md) passed the conditional factorization and contradiction; it does not establish Lean acceptance or provider compatibility.

The held runner's `selection.json` compares current direct-source-import first selections across both producer paths and the proposed join path; it rechecks that capture before and after the run. Full serialized transitive/package and producer-time ancestry is not captured. The [independent prelaunch review](../../reviews/trace74-n5-r9-scalar-discrete-prelaunch-independent/README.md) approved one coordinated check.

One author run completed in actual tool session 34480, exit 0 and fully reaped. Its [terminal](observations/attempt01/terminal.json) SHA-256 is `fda1b476495f901f3c217a616a41a2f316aea9fbb13cca1b5cdc250066e1b865`; object `/tmp/trace74-n5-r9-scalar-join-edinztzy/lib/Trace74N5R9ScalarDiscrete.olean` SHA-256 is `0a338104a9091d4dff6002e47fa466973e7c4406da4b5d33ea2440bcac5ab384`. The conditional theorem passed, as did the [independent result audit](../../reviews/trace74-n5-r9-scalar-discrete-result-independent/README.md).
