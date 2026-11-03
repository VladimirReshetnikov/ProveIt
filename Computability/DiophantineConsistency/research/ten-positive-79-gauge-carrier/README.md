# Corrected 79-row main-carrier gauge

`Mask79Carrier.preserve_rank_and_main` proves an identity in every commutative ring. With

```text
D = q*(K+w)+1,       F′ = F+b*t,       C′ = C−q*b*t,
n′ = n−(b*v+1)*D*t,  B = (K+w)*C−F,
```

the rank term `q*(q−F)−C` is preserved, and so is

```text
(b*u)*(H*(n−v*B)+Z) − H*(u*B+b*P).
```

For the 79-row graph, row inspection gives `b=r01`, `v=r52`, `u=r53`, `H=r16`, `Z=r62`, `P=r33`, and `r54=b*u`; the displayed expression is then row 69. This corrects the [earlier update](../ten-positive-79-gauge-normalization/README.md), which preserved the inner residual but overlooked the separate `u*B` term. The Lean theorem checks the generic algebra, not the interpretation of the graph rows or full output invariance.

Positive-witness normalization still requires finding a natural `t` with `q*b*t<C`, `(b*v+1)*D*t<n`, and the new guard `F′+C′<q`. Since the actual graph has `q=b+1`, a sufficient form of the guard is `F+C<q+b^2*t`; the positivity inequalities are strict. No existence theorem for such a `t`, no model-zero equivalence and no 79-operation iPRA theorem is claimed. For example `q=2`, `b=1`, `F=C=1` leaves no positive `C′` when `t≥1`, while `t=0` leaves the guard false; this is only an arbitrary positive assignment, not a claimed graph zero.

Guarded author `observations/attempt01/` and its enclosing tool session exited 0. Source SHA-256 is `18914e4c498aedd82dbff48db47b318e6d822b74a92dba2630a885434093af39`; terminal SHA-256 is `4f81e10f28e8babe452258e713c62b2c472d475b8cf49428aa4f07bbfad72149`; output `/tmp/mask79-carrier-w290b5ah/Mask79Carrier.olean` has SHA-256 `a880a3df700be3af796282b0600161756e640ad7da78fdcb383fa49b1c2f5b60`. The direct Mathlib ring tactic object and Lean executable are pinned; transitive package/dynamic ancestry remains inherited and no independent Lean replay is claimed.

**Later result:** the [signed-gauge obstruction](../ten-positive-79-gauge-signed-obstruction/README.md) proves that this exact gauge cannot turn an unguarded valuation with positive F into any guarded model-natural valuation, for either sign of the difference-ring parameter. The conditional statements above remain valid; the obstruction does not decide unrestricted 79 equivalence or a different transformation.
