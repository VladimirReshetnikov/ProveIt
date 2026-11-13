# Positive first-root branch

`Absorb89PositiveBranch.graph_growth` combines the checked index chain with the conditional Pell growth lemma to establish `3*s ≤ k` for every positive zero of the actual 89-row graph in an IΣ₁ model, under the port bounds `0 < beta`, `low < beta`, and `high < 2*beta`.

`positive_branch` adds the displayed positive signed first-root equation, the first norm and positivity of the transport term; it then proves `s < r`. Divisibility by `b=J*beta` is obtained from the actual graph zero, and cancellation uses its positivity. The assumptions and exact model expressions are explicit in the source. This is one branch only; it does not by itself prove the reverse witness map, halt equivalence or iPRA equivalence.

`run-positive-branch.py` used the captured selected provider and checked chain objects. Author attempt01 failed on a local rewrite and is preserved. Attempt02 passed in guarded session 81526 with exit 0 and no reported warnings, output `/tmp/absorb89-chain-zbhcy0_l`; exact sources, commands, resource samples, object hashes and stdout are in `observations/positive-branch-attempt02/`. This is not an independent Lean replay; package-transitive, dynamic and historical source/object ancestry are inherited limitations.
