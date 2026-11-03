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
