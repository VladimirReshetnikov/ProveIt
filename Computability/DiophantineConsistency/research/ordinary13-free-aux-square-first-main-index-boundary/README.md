# Two norms force a late main index in the fixed X=q slice

In the [84-row free auxiliary-square candidate](../ordinary13-free-aux-square-compact-factor-obstruction/candidate.json), at the fixed symbolic compact ports with `J=1`, `w=1` and `s=1`, at a standard-integer output zero, every **positive** Pell index m representing its actual main ordinate must satisfy `m>q²`, where `q=2^(67*8807)`. Equivalently, the first and main residuals cannot both vanish in this slice with `c=y_m(a)` and `1≤m≤q²`. This strengthens the [early m<N bound](../ordinary13-free-aux-square-early-main-index-obstruction/README.md) and includes m=N. It is not a global no-zero proof, zero-map, model theorem or Lean/iPRA endpoint.

The statement uses the eta/zeta-natural graph, whose `k=eta+zeta` has **no extra +1**. At a putative main zero, U=q⁵>0 and `c=eta+q³k` is a natural Pell ordinate. If m≥1 then c>0. If k=0, natural `k=eta+zeta` forces eta=0 and hence c=0, contradiction. Thus k>0 is established here directly; no shifted-zeta positivity theorem is assumed. A main zero with c=0 is outside this index statement.

At an ordinary integer product zero, all four factors are units. The exact first and main factor shapes cannot be −1 modulo four; the checker exhausts those residue patterns. Hence both A0 and A1 vanish. In the argument below they may equivalently be taken as explicit hypotheses, without using product extraction.

Write beta=q−1, `F=n_F+1≥1`, `alpha=n_alpha+1≥1`, `C=q−F−alpha`, `B=C(q+K0)−F`, and `ell=q⁷k`. If C≤0, natural K0 makes B<0. The exact first root is then strictly greater than `beta(ell+k)`, whose square is at least its required norm because `ell*k+k²−1≥0`. Thus C>0, so F+alpha<q. The graph rank is

```
G=alpha+(q−F)(q−1),
R=G(q²−1)+MC+q*MF.
```

The strict gap gives `2q−1≤G<q²`; the fixed tuple gives `0≤MC<q` and `0≤MF<2q`. Therefore, for q≥8,

```
2q² < R+1 < q⁵.                         (1)
```

From the signed first norm, standard first-Pell descent gives a natural index n≥1 and `k=2*y_n(2q⁷+1)`, with `k≡2n (mod 4q⁷)`. The actual signed main-root equation and positive U=q⁵ give `q⁵ | H(R+1−k)`; H=4a+3 is odd, so `k≡R+1 (mod q⁵)`. Thus

```
2n ≡ R+1 (mod q⁵).                       (2)
```

To bound n, the natural Pell recurrence has `A^(j−1)≤y_j(A)≤(2A)^(j−1)` for A≥2 and j≥1. The first multiplier is `2q⁷+1`, the main multiplier is `q³(q+1)+2`, and `2*(q³(q+1)+2)<q⁵` for q≥8. If n>m, then

```
c ≥ q³k ≥ 2q^(7(n−1)+3) ≥ 2q^(7m+3),
c = y_m ≤ q^(5(m−1)),
```

which is impossible. Therefore n≤m. If m≤q², this gives `2n≤2q²<R+1<q⁵`, contradicting (2). No chosen sign of either signed root is required.

The checker pins the exact child/source, reproduces the early-index receipt, verifies graph wiring and both modulo-four factor exclusions, proves the stated q≥8 growth/rank inequalities by nonnegative polynomial coefficients, and checks bounded Pell controls. The standard Pell classification, inequalities and divisibility proof above supply the general argument; no giant fixed numbers or Pell iterates are materialized. It remains limited to J=1, X=q, s=1 and positive indexed c; no Lean, provider/axiom audit, actual full-zero existence or PDF binding is claimed. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-aux-square-first-main-index-boundary/check.py | cmp - research/ordinary13-free-aux-square-first-main-index-boundary/receipt.json
```
