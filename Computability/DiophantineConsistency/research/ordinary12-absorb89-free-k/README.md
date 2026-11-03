# Why deleting the `k = eta + zeta` gate needs new soundness

The variable `zeta` occurs in the 89 graph only through `k = eta + zeta`. Replacing that sum by an independent positive `k` would remove one operation, but it drops the existing invariant `eta < k`. The established halt-soundness chain uses this invariant in `ArithmeticPellPowerRecovery.power_bound`: it turns `c=kY+eta` into `c<k(Y+1)` and derives `2^(2r+1)<Y` from the Pell coordinates.

`check.py` gives an exact natural-number witness to the failure of that particular inference without `eta < k`. For `X=16`, `Y=1`, `r=2`, the two specified Pell ordinate formulas give `k=8710` and `c=2080805`; `eta=c-kY=2072095` is positive, but `2^(2r+1)=32` is not less than `Y`. Its recurrence is the same recurrence as `ArithmeticPellRecurrence` and uses integer arithmetic only.

This is not a counterexample to the full graph or to a different soundness argument: the port, rank, ordinary-residual, and other hypotheses are not established for this tuple. It shows that removing the gate cannot be justified merely by dropping the positivity of `zeta` from the existing coordinate-growth lemma. No 88-row equation or equivalence is asserted.
