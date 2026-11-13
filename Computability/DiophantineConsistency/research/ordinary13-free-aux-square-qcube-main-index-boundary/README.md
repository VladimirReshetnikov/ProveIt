# Sharpened fixed-slice main-index boundary: m>q³

This source-only follow-up strengthens the [q² positive-index boundary](../ordinary13-free-aux-square-first-main-index-boundary/README.md). At the fixed symbolic compact tuple, for an ordinary-integer zero of the free auxiliary-square candidate with `J=1`, `w=s=1`, every main Pell index representing its actual ordinate satisfies `m>q³`, where q=2^(67*8807). The separate [two-norm transfer](../ordinary13-free-aux-square-two-norm-positive-k-transfer/README.md) excludes k=0 and c=0, so m=0 is not silently discarded. This is not a global no-zero, zero map or Lean/iPRA theorem.

The q² packet's proof supplies, under the two actual first/main norms and this slice's fixed compact bounds, positive indices n,m and

```
2q² < R+1 < q⁵,
2n ≡ R+1 (mod q⁵),
c ≥ 2q^(7(n−1)+3),
c ≤ q^(5(m−1)),
R+1 ≥ (2q−1)(q²−1)+1.
```

The strict gap between the two growth bounds is stronger than n≤m: because q>1, it gives

```
7(n−1)+3 < 5(m−1),  hence  7n+1 < 5m.        (1)
```

Suppose m≤q³. Then `14n<10m≤10q³`. For q≥8, the rank lower bound gives

```
7(R+1)−10q³ ≥ 4q³−7q²−14q+14 > 0.
```

Thus `2n<R+1<q⁵`, contradicting the q⁵ congruence. The positive polynomial on the right is checked by nonnegative coefficients after q=8+t. The separate two-norm transfer checks the exact first/main graph trees and product-factor exclusions, then derives `k>0` at the natural compact port bounds; `c=eta+q³k>0` excludes Pell index zero. Standard integer Pell classification supplies an index for the natural main norm. Those source and written arithmetic arguments have not been elaborated in Lean.

The checker reproduces both predecessor receipts and checks the sharpened exponent/rank inequalities and bounded controls without constructing the fixed q or Pell numbers. Other J, w or s values and main indices above q³ remain open. No actual zero, parent-child zero equivalence, provider/axiom replay or PDF binding is asserted. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-aux-square-qcube-main-index-boundary/check.py | cmp - research/ordinary13-free-aux-square-qcube-main-index-boundary/receipt.json
```
