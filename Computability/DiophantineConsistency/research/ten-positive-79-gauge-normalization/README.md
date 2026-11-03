# Candidate 79-row gauge normalization

`Mask79Gauge.preserve_rank_and_carrier` proves two identities in every commutative ring. Write

```text
G = q*(q−F)−C,             B = (K+w)*C−F,
F′ = F+d,                  C′ = C−q*d,
n′ = n−v*(q*(K+w)+1)*d.
```

Then `G′ = G` and `n′−v*B′ = n−v*B`. In the 79-row graph, row 52 is a square that is unchanged when `G` is unchanged, so the second identity preserves row 56 when `v` is that square. **This does not preserve the full carrier**: row 65 separately contains `r53*B`. Writing `D=q*(K+w)+1`, the proposed update changes row 69 by `+r16*r53*D*d` in general. The checked Lean result is only the two displayed ring identities.

A possible normalization would choose a nonnegative natural `d` that also preserves strictly positive witnesses and supplies the missing guard. For `q ≥ 1` and nonnegative `v`, `K`, `w`, `d`, sufficient conditions include `q*d < C`, `v*(q*(K+w)+1)*d < n`, and `F+C < q+(q−1)*d`; these guarantee positive `C′`, positive `n′`, and `F′+C′ < q` when the original positive witnesses and ordinary natural arithmetic apply. The existence of such a `d` for every positive graph zero is **not proved**, nor are these inequalities asserted as necessary. No unrestricted 79-row equivalence, iPRA theorem or operation reduction follows from this packet. For example, the positive assignment `q=2`, `F=1`, `C=1` already violates the guard, and every natural `d≥1` makes `C′≤0`; `d=0` leaves the guard false. This only obstructs the proposed normalization on arbitrary positive assignments; it is not claimed to be a graph zero.

Guarded author `observations/attempt01/` and its enclosing tool session exited 0. The source SHA-256 is `110a921aadd1b0a60c790fab7246c64693a86feb1f11fcc6ac6ba949d428c8c2`; terminal SHA-256 is `d557f2d79a82c19155aa048cf14ffaccec6e03ac34f3241069bb206d8f09c2ba`; the output `/tmp/mask79-gauge-j1gnsjjn/Mask79Gauge.olean` has SHA-256 `d73aa1f17c8f6608e0bbbf72ff7c71fb0827daac337b637bf7845691796a5f48`. The direct Mathlib ring tactic object and Lean executable are pinned; transitive package/dynamic ancestry is inherited, and no independent Lean replay is claimed.

**Later result:** the [signed-gauge obstruction](../ten-positive-79-gauge-signed-obstruction/README.md) proves that the exact corrected gauge cannot turn an unguarded valuation with positive F into a guarded model-natural valuation for either sign of its difference-ring parameter. This does not decide unrestricted 79 equivalence or rule out another transformation.
