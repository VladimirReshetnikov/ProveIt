# Bounded first-index screen with the quartic rank window

This is a finite search of a small, **noncompact44** family: `beta=2`, `J=1`,
`q=3`, `F=alpha=1`, `R∈{43,47}`, `1≤s≤300`, `1≤w≤10000`, and first
Pell index `1≤j≤R`. Both ranks occur with nonnegative masks `MC<beta`,
`MF<2beta`: use `(MC,MF)=(0,1)` for 43 and `(1,2)` for 47. They obey
`R+1<q⁴`. The search assumes the main index is `m=R` and `Y=27s`,
`X=3w`; it allows values that may not satisfy positive transport, so it
screens a superset of those particular transport-valid inputs. It does not
apply to the fixed compact44 ports, whose beta is much larger.

For each tuple, put `U=Y²`, `a=(X+1)Y`, `H=4a+3`, and let `(g,c)`
be the positive Pell pair at index `R`. The free carrier implies
`H | U(2^R−X)` by the Pell projection identity, so the checker uses this
exact integer divisibility as a necessary filter. For each survivor it
computes the Pell pair with exact integer arithmetic, verifies the actual
carrier division and positivity, and enumerates the first Pell pairs with
index `1≤j≤R`. The required positive `eta,zeta` are equivalent to
`Yk<c<(Y+1)k`; the loop stops once `Yk≥c` because the positive first Pell
coefficient increases with the index. It does not assert that an index
above `R` cannot work.

The complete stated search has four projection survivors with positive
carrier, `(R,s,w)=(43,57,24), (47,8,6351), (47,46,48), (47,84,24)`,
and none meets the first/main scale inequality for `1≤j≤R`. It has no
nonpositive-carrier survivor. The first result at `R=47,s=8` is also in
the earlier divisor-enumeration screen; the earlier `(47,26,10021896201)`
result lies outside this packet's `w` range. The screen neither proves the
old first-index congruence nor rules out a zero elsewhere, and it does not
check the strong, auxiliary, or full graph equations.

Run `python3 -I -S -B check.py`; the graph pin, exact output and the precise
domain are in [result.json](result.json). Arithmetic is finite and exact;
no Lean theorem is claimed.
