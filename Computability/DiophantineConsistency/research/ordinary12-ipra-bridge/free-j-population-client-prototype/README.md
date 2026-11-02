# Free-J population client: uncompiled source draft

These two files are an **uncompiled draft**. `FreeJPopulationFactsNarrow.lean`
is the paired graph-independent argument with its import narrowed to
`ArithmeticHalfBinomialCompat`; it has not been checked with that import.
`FreeJPopulationClient.lean` proposes applying it to the free-J graph's exact
ordinary-index and power theorems. It explicitly retains the positive port and
variable hypotheses, β ≥ 46, graph zero, and `q = 2^h`; it does not specialize
the compact44 ports or prove a PRA theorem.

The preferred coherent route and its nine-module source/dependency observation
are in `free-j-population-closure-plan`. The draft must be checked by a
source-frozen, matched author/peer rebuild against the audited free-J provider;
no objects from the incompatible endpoint provider may be mixed into it.

The proposed driver strips Python-related variables and `LEAN_SRC_PATH`,
`LEAN_SYSROOT`, `LD_LIBRARY_PATH`, `LD_PRELOAD`, and `LD_AUDIT` before Lean
compilation, then sets the same-side `LEAN_PATH`. Project imports under
`DiophantineConsistency` must resolve in that same-side overlay; they cannot
fall back to the package library. The driver checks the exact names and allowed
axioms of the two printed client declarations. Compilers use the sampled
leader/process-group monitor; the separate `lean --deps` query uses a
60-second subprocess timeout, not that resource monitor, and the read-only
audits use timeouts rather than a hard resource quota. This is a description
of the proposed replay, not evidence it has run.

The first protected paired wrapper, session 52770, exited 1: the first six
author modules succeeded, then `ArithmeticBinomLegendre` itself exited 0 but
the strict driver rejected its `unnecessarySimpa` warning at line 78:10. No
peer build or graph theorem resulted. The pinned source remains unchanged and
the exact failure logs and original driver are retained. The revised driver
accepts only that complete observed warning text for that exact module and
frozen source location; any changed or additional warning is rejected. It does
not suppress that linter or accept a warning class generally. The isolated
`warning_controls.py` run exited 0 after testing the observed warning and
changed-line, extra-warning, wrong-module and missing-warning controls; its
isolated `-O` run was rejected with exit 1. A fresh independent prelaunch
review and protected paired run are still required.

After the first failed pair, an exploratory continuation used a new overlay of
the retained author-side partial provider, leaving its objects and logs intact.
The first temporary launcher exited 1 before Lean because of a monitor-loader
typo; corrected wrapper session 36556 exited 0 for all four remaining modules,
including the graph client, with no warnings or sorryAx. Its source and logs
are retained under `observations/author-continuation`. This is single-side
exploratory evidence and does not replace the required matched replay.
