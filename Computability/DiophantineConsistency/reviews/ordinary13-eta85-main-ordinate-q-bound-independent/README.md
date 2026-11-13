# Independent review: main norm and k>q

The [reviewed argument](../../research/ordinary13-eta85-main-ordinate-q-bound/README.md) soundly derives `k>q` over the ordinary naturals from the **main residual being zero** and q≥2, for the pinned eta-natural prototype and its F- and alpha-unshift probes. I found no error in the square gap, inverse Pell descent or interval estimates. This does not extract the main residual from a product-output zero, prove a reverse zero map, or establish a model/Lean/iPRA theorem.

All three checked graphs have `s=n_s+1`, `k=eta+n_zeta+1`, `Y=q³s`, `X=q*w`, `c=Yk+eta`, `a=Y(X+1)`, `U=Yq²` and `Delta=(a+2)²−1`. Thus k≥1, 0≤eta≤k−1, Y≥q³ and U>0. These statements concern the **positive-zeta parent** with its +1; they should not be silently transferred to the separate eta/zeta-natural probe where k may be zero. The author's checker pins the parent and F probe; this review also pins and checks the alpha probe's exact main circuit.

A zero main residual gives `Dstar²=U²(1+Delta*c²)`. Integer square divisibility makes U divide Dstar; taking its absolute quotient gives nonnegative d with `d²−(A²−1)c²=1`, where A=a+2. For 1<c<2A, the radicand lies strictly between `(Ac−1)²` and `(Ac)²`, because the difference above the lower square is `c(2A−c)` and the difference below the upper square is `c²−1`.

For the remaining interval, positivity of d and the norm give `(A−1)c<d<Ac`; hence `t=Ac−d` is a positive integer smaller than c. The inverse coordinate `d'=Ad−(A²−1)c` is positive: the difference of the two relevant squares is `A²+(A²−1)c²`. The exact identities give `d'²−(A²−1)t²=1` and `c=d'+At`. If c<2A², then t<2A. The first square gap forces t=1, whence d'=A and c=2A. Therefore no solution has `2A<c<2A²`.

Assuming k≤q gives `1<c≤qY+q−1≤Y²+Y−1`. If w>0, X≥q makes c<2A. If w=0, A=Y+2; k=1 or 2 again gives c<2A, while k≥3 gives `2A<c<2A²`, since Y≥8. Both cases contradict the norm. These inequalities use no F, alpha, first-factor or compact-mask premise beyond the exact graph definitions and q≥2.

The receipt reproduces the author's checker, independently verifies the polynomial inverse/square-gap identities and all three graph circuits, and enumerates 347,600 bounded Pell candidates, finding only c=2A in the relevant interval. The bounded controls do not replace the general argument and no Lean or provider validation was run. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-eta85-main-ordinate-q-bound-independent/check.py | cmp - reviews/ordinary13-eta85-main-ordinate-q-bound-independent/receipt.json
```
