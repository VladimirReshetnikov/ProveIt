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
