# Failed symbolic-kernel link attempt

The source attempts to connect the earlier `kernelNat` definition to `paramKernel rho`, making `rho` locally irreducible and expanding only named definitions with `simp only`. Lean session 33133 actually exited 1 at the 3,000 MB kernel limit. The compiler log's axiom report includes the failed declaration itself and is not evidence of a theorem. This retains the attempt without changing either of the successful earlier author-only generic and parameterized cast results.

The concrete K link remains open, as do equality to retained bytes or the selected expression, the graph/checker semantics, and any internal iPRA conclusion. This was a single-side exploratory test on the earlier overlay, not a paired or independently audited replay.
