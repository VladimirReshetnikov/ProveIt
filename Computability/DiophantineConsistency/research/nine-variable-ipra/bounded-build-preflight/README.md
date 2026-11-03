# Nine-variable source-declared build preflight

[`scan.py`](scan.py) traverses source-declared imports after removing nested
Lean comments and strings, consults the repository's `lean_lib` source roots,
and samples object availability in the existing standard-QM40 author overlay,
Foundation package root and Lean toolchain. It does **not** invoke Lean.
[`REPORT.json`](REPORT.json) records the exact topological list and source
hashes observed on this worktree.

At this observation, `IPRANineCurrent` had 1,188 project sources in its
source-declared closure, with 80 corresponding objects absent in the sampled
roots. `IPRAExplicitZFCFinal` had 1,035 sources and 93 absent objects. The
missing sets share 70 objects, for 103 in the union. No project source or
directly named external import object was missing in the sampled paths. The
ordered plan visits `IPRANineCurrent` at stage 80 and
`IPRAExplicitZFCFinal` at stage 103; `Diophantine.Common.MRDPCore` appears
at stage 33. This is a source-derived order, not a record of compilations.

For the 1,108 and 942 project objects already present, the scan also tries
to locate a corresponding `src` snapshot next to the object's resolved
provider. It found 97 and 79 matching source files, no differing files among
those found, and no candidate source snapshot for 1,011 and 863 objects,
respectively. The inferred source location is only a heuristic: matching
bytes do not prove that they produced the object, and an unavailable snapshot
does not prove source drift. In particular, object presence alone does not
authenticate the current source closure.

The first feasible build route is a new isolated overlay based on
`/tmp/ipra-standard-qm40-author-run-02/lib`, followed by the 103 stages in the
recorded order. Each stage needs its source and direct imports pinned, an
unoccupied output slot, a 3 GB Lean kernel limit, one Lean process at a time,
a bounded timeout, and preserved success or failure evidence. The previous
author overlay and package roots retain their transitive and dynamic ancestry;
the scan does not authenticate them, derive their actual binary import graph,
or establish a paired replay. At observation about 15.9 GiB was free; the
planned build must enforce at least 4 GiB free before each stage, and actual
per-stage memory, runtime and disk growth remain unmeasured.

Reproduce from the repository root with `python3 -I -S` on `scan.py`. The
output is a fresh sampled JSON report; its time and free-space fields can
change. Optimized Python is rejected. Source or provider changes require a
new preflight rather than silently reusing this order.

## Prepared incremental runner

[`replay.py`](replay.py) is a resumable, single-side experiment over the
pinned overlay. It adds `IPRANineChecks` immediately after the NineCurrent
endpoint, for 104 stages total. It freezes every planned source, checks the
recorded standard-QM40 and native parent guards, and checks declared direct
imports and all recorded module companions before each build. Successful
objects are published without overwrite and recorded in a contiguous receipt
ledger; failed attempts are retained separately. Each compiler step uses
`-M3000 -j1`, a 600-second timeout, strict rejection of warnings and
`sorryAx`, and a 4 GiB free-space floor. The two endpoint audit stages require
the expected axiom-report names and allow only `propext`, `Classical.choice`,
and `Quot.sound`.

Initialize a fresh direct `/tmp` child with `--init`; `--check` verifies its
inputs and ledger without invoking Lean. To execute, use the same command
without either flag; the default is one stage per invocation and `--limit N`
allows up to N stages. The process lock excludes simultaneous users of the
same overlay. An interrupted publication that leaves an object without a
receipt is reported for inspection and is not silently removed or resumed.

The exact runner was initialized at `/tmp/nine-ipra-guarded-author-20261102-e`
and `--check` reported zero completed stages with `WeightedExpressionDegree`
next. An overlay made with an earlier runner was rejected for runner drift,
and optimized Python was rejected. These are initialization/control checks:
**no compiler stage was launched by these checks**. The compiler path,
warning behavior on these 104 sources, resource usage and full resumption
after a real stage remain untested. Direct-input guards are sampled at stage
boundaries; the inherited package, transitive and dynamic provider ancestry
is not authenticated.
