# A limitation of directly absorbing the ordinary witness

The 89-row ordinary residual uses `(V+n)^2`. Replacing `V+n` by a positive independent witness `h` deletes one addition, but the reverse map would need a sign of `h` with `n = ±h-V > 0` while preserving that square. The isolated residual does not guarantee such a sign. `check.py` gives the exact example `c=2`, `Q=64`, `V=1`, `h=1`: the ordinary residual is zero, but both possible values of `n` are nonpositive. No floating-point computation is involved.

This is an obstruction to a proof based solely on the isolated ordinary residual. It is not a full-graph counterexample: the example does not claim that these parameters satisfy the other graph equations, port constraints, or the definitions of `Q` and `V`. A graph-specific argument or another construction could still make an 88-row reduction work. No new equation or equivalence is asserted here.

Deleting the `f=1+t` addition and treating `f` as merely positive also needs a new argument: `f=1` makes `Q=0`. Then choosing `T=1` gives `V=-R`, and `n=R+1` makes the ordinary residual zero, for every positive `c` and natural `R`. This follows by substituting `Q=0` into the polynomial; the checker samples the identity. It shows that the ordinary factor alone cannot exclude the newly admitted value `f=1`. It does not assert the other residuals vanish.
