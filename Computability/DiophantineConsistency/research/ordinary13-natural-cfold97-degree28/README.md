# Thirteen natural inputs: 97 operations, degree 28

This proposed graph translates the independently reviewed
[13/88/28 positive C-fold graph](../ordinary13-cfold88-28/) to 13
nonnegative inputs with 97 live binary operations and exact degree 28 at
the authenticated compact44 ports. It has the same natural-zero existence
as the positive parent's zero existence under the parent's fixed-port
hypotheses and **the same sign-free calibration replay**. In particular,
the argument below uses `beta>=46`, `K0>=0`, `0<MC<beta`, and
`0<MF<2*beta`, together with the fact-level conclusion `X>=q²` established
in the cited calibration under its stated hypotheses. This external
application has an [independent review](../../reviews/ordinary13-natural-cfold97-degree28-independent/README.md), but is not a Lean/iPRA theorem,
PDF or coefficient-byte binding, fresh provider replay, or minimality claim.

## Graph edit and two transfers

The positive parent uses coordinates

```
J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma.
```

Use `n_J`, `n_f`, and `n_r` directly, increment the other ten natural
coordinates, and fold the zeta increment into

```
kbase=(n_eta+1)+n_zeta,  k=kbase+1,  r0=kbase−R.
```

The unchanged parent `k` and `r0=k−R−1` are thus recovered. The complete
graph edit adds nine live gates to the 88 parent. For arbitrary signed
integers and ports the new polynomial equals the parent polynomial under
these affine substitutions. A positive parent zero maps to a natural new
zero by subtracting one at the ten incremented coordinates.

Conversely, let the new graph vanish at natural inputs. Its output is the
sum of four integer squares, so all four residuals vanish. All parent
coordinates except possibly `J`, `f`, and `r` are positive.

* If `f=0`, then `Q=Delta*(f²−1)=−Delta<0`, while the strong residual
  `I²−Q=0` requires `Q=I²>=0`; here `Delta=a²+4a+3>0` because `X,Y>0`.
  Therefore `f>0`.
* If `J=0`, then `b=J*beta=0`, `q=1`, `M=q³*b=0`, and
  `C=1−F−alpha<0`. Since `X>=1`, `K0>=0`, and `F>=1`,
  `Bt=C*(X+K0*q)−F*q<0`. The first root expression
  `Z=M*(ell+k+r−k*C)+Y*b−q³*Bt` equals `−Bt>0`, contradicting
  its vanishing residual `Z²=M²*(1+ell*(ell+k))=0`. Thus `J>0`.

If `r>0`, the affine identity now gives a positive parent zero. If `r=0`,
use the positive-root repair below, leaving all other coordinates fixed.

## Positive-root repair at r=0

Write `b=J*beta`, `q=b+1`, `M=q³*b`, `m=X*Y²`, `k=eta+zeta`,
`ell=m*k`, and `Bt=C*(X+K0*q)−F*q`. The first residual says

```
Z²=M²*(1+ell*(ell+k)),
Z=M*(ell+k+r−k*C)+Y*b−q³*Bt.
```

If `C<=0`, then `Bt<0` and, even allowing `r=0`,
`Z>M*(ell+k)`. This is impossible because `k>=2`, `ell>0`, and
`(ell+k)²>1+ell*(ell+k)`. Hence `C>0`. The norm gives `M | Z`; reducing
the displayed expression modulo `q³` and `b`, which are coprime, gives
`q³ | Y` and `b | Bt`. Set `s=Y/q³>0`, `t=Bt/b`, and `tau=|Z|/M>0`.

All hypotheses needed for the parent's sign-free fact-level calibration
hold: the non-root coordinates are positive, `C>0`, the four residuals
vanish, and the fixed-port bounds above hold. As in the reviewed C-fold
packet, its conclusion `X>=q²` gives `Bt−C>0`, so `t>=1`. The independently
reviewed first-Pell and main-norm argument in
[`folded-root86-negated-positive-bt`](../ordinary13-folded-root86-negated-positive-bt/)
then gives `tau−ell>2*s`; it uses the positive non-root coordinates and
the two norms, not positivity of the present folded-root coordinate.

Choose instead the positive-root coordinate

```
r_plus = (C−1)*k + (tau−ell) − s + t > 0.
```

Substitution yields `Z=M*tau`, so the first residual remains zero; the
other three residuals do not depend on `r`. This explicitly maps the
natural zero to a positive parent zero. The two existence maps need not be
pointwise inverses because this step may switch a Pell root.

## Count, degree and scope

All 97 binary operations, 13 inputs and four fixed ports are live. Affine
substitution preserves the parent's degree-28 upper bound. The all-inputs-
equal ray at authenticated P72/P115 ports has degree 28 modulo
1,000,000,007 with leading coefficient 59132194, proving exact specialized
integer degree 28. The checker pins both graphs and port bytes, verifies the
gate edit and liveness, tests 300 signed modular identities, verifies the
listed finite port bounds, and computes that ray. Its finite checks do not
prove the unbounded root-repair, calibration replay, or inherited endpoint.

Against the separate proposed [13/88/99 natural graph](../ordinary13-natural-unit-product88/),
this candidate trades nine operations for degree 28 instead of 99; neither
dominates the other in those two measures. This is not a global frontier
claim.

```
python3 -I -S -B research/ordinary13-natural-cfold97-degree28/check.py > /tmp/natural13-cfold97.json
cmp /tmp/natural13-cfold97.json research/ordinary13-natural-cfold97-degree28/result.json
```
