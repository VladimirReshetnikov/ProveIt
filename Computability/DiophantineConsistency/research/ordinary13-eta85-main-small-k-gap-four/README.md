# Main norm excludes k≤4 for the eta/zeta parent

For the exact 85-row eta/zeta parent, assume ordinary nonnegative witness coordinates, natural ports, q≥2, and a vanishing **main residual**. Then `k=eta+n_zeta+1≥5`. This is a main-norm consequence, independent of F, alpha, the first residual and the compact mask values. It also applies to the 84-row F and alpha probes, which leave the relevant main fields unchanged. Extracting the main residual from a full product zero and transporting the argument to arithmetic models are separate steps.

Write `Y=q³s≥8`, `a=Y*(X+1)`, `A=a+2`, and `c=Y*k+eta`. The preceding [small-k audit](../ordinary13-eta85-Fzero-positive-gap-boundary/) gives the consecutive-square gap for `1<c<2A`, excluding k=1 and 2.

For k=3 or 4, `0≤eta≤k−1` and X≥0. If X≥1, then `a≥2Y` and

```text
1<c≤4Y+3<4Y+4≤2A,
```

so the same gap applies. If X=0 then a=Y and

```text
2A=2Y+4<c≤4Y+3<4A=4Y+8,
```

using Y≥8. In this second interval the main radicand lies strictly between a different pair of consecutive integer squares:

```text
1+(A²−1)c² − (Ac−2)² = c*(4A−c)−3 > 0,
(Ac−1)² − (1+(A²−1)c²) = c*(c−2A) > 0.
```

The first is positive because both integer factors are positive and c≥2A+1≥5. The main norm `Dstar²=U²*(1+(A²−1)c²)` with positive integer `U=Yq²` would make the radicand a square, by square divisibility; contradiction. Thus the open F=0 positive-gap branch, assuming its main norm, starts at k≥5 rather than k≥3.

The checker pins and reproduces the earlier receipt, checks the exact relevant parent rows and both new polynomial identities, and tests bounded nonnegative cases. The uniform interval and square argument is stated above; finite tests do not replace it. No Lean, build, model or endpoint claim is made.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-eta85-main-small-k-gap-four/check.py | cmp - research/ordinary13-eta85-main-small-k-gap-four/receipt.json
```
