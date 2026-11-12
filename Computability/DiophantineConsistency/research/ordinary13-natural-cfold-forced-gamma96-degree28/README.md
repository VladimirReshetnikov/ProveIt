# Forced gamma in the C-fold graph: 13 natural inputs, 96 operations, degree 28

This proposed graph deletes `gamma=n_gamma+1` from the proposed
[13/97/28 natural C-fold graph](../ordinary13-natural-cfold97-degree28/)
and uses the natural input directly. It has 13 nonnegative inputs, 96 live
binary operations and exact degree 28 at the authenticated compact44 ports.
The zero maps use integer ports with `beta>=46`, `K0>=0`, `0<MC<beta`,
`0<MF<2*beta`, the rank-window theorem, and elementary Pell descent. The
authenticated ports satisfy these bounds. This external argument has an
[independent review](../../reviews/ordinary13-natural-cfold-forced-gamma96-degree28-independent/README.md); it is not a Lean/iPRA theorem,
PDF or byte binding, fresh provider replay, or minimality claim.

## Graph and zero maps

The only graph edit deletes the gamma increment and retargets its consumer.
For arbitrary signed integers, the new output at `gamma=g` equals the 97
output at `n_gamma=g−1`, with all other coordinates unchanged. Any natural
97 zero maps to the new graph by incrementing `n_gamma`. Conversely, the
argument below forces `gamma>0` at any new natural zero; subtracting one
then gives a 97 natural zero. The two maps are inverse on zeros.

## Consequences independent of gamma

The output is a sum of four integer squares, so all norm residuals vanish.
The J and f positivity arguments and the first-norm proof of `C>0` in the
97 packet use only natural `gamma` and do not require it to be positive:
in particular, if `C<=0`, then `Bt<0` and the first root expression is
strictly greater than `M*(ell+k)`, contradicting its norm. Thus

```
J>0, f>0, b=J*beta>0, q=b+1>=2, C=q−F−alpha>0,
M=q³*b, U=Y*q², m=X*Y², k=eta+zeta>=2, ell=m*k.
```

The shifted coordinates keep `F,alpha,X,Y,eta,zeta` positive. The first
norm gives `M | Z`. Its root expression

```
Z=M*(ell+k+r−k*C)+Y*b−q³*Bt
```

therefore implies `q³ | Y` because `gcd(q³,b)=1`; hence `Y>=q³`.
The stated port bounds and `F+alpha<q` match
`ArithmeticAdaptiveRankWindow2011.scalar_rank_window`, giving
`R+q³+q+1<=q⁴`, so `R+1<q⁴`. Its application is external fact-level
mathematics; the checker does not elaborate or replay that theorem.

Let `a=XY+Y`, `c=eta+Y*k`, `H=3+4*a`, and `Delta=(a+2)²−1`. The main
norm gives `U | Dstar` and an integer `d_abs=|Dstar|/U` satisfying
`d_abs²=1+Delta*c²`. If `k=2`, then `eta=zeta=1`, `c=2Y+1`, and
`1<c<2*(a+2)`, so that square lies strictly between
`((a+2)*c−1)²` and `((a+2)*c)²`, contradiction. Thus `k>2`. The first
norm gives `tau²−m*(m+1)*k²=1` for the natural integer `tau=|Z|/M`.
The independently reviewed elementary descent in
[`folded-root86-negated-positive-bt`](../ordinary13-folded-root86-negated-positive-bt/)
therefore yields `k>=8*m+4`.

Set `E=X*Y`. Since `X>=1`, `Y>=q³`, and `q>=2`,

```
k−E*q >= X*Y*(8*Y−q)+4 > q⁴ > R+1,
c=eta+Y*k > X.
```

## Gamma cannot vanish

If `gamma=0`, the main expression is

```
Dstar=U*(X+a*c)+H*(E*q+R+1−k).
```

It remains positive: `c>Y*k`, `E*q+R+1>=0`, and
`U*a*Y=Y²*q²*a>H` because `q>=2`, `Y>=q³`, and `a>=1`; hence
`U*a*c>H*k`. Thus `d=Dstar/U` is positive. The main norm implies

```
d²−((a+1)*c)²=(2*a+2)*c²+1>0,
```

so `d>(a+1)*c>X+a*c`. Rearranging Dstar gives

```
0 < U*(d−X−a*c)=H*(E*q+R+1−k)<0,
```

contradiction. Therefore `gamma>0`, without a positive-gamma premise.

## Count and degree

All 96 binary gates, 13 inputs and four ports are live. The affine edit
preserves the parent's degree-28 upper bound. The all-inputs-equal ray at
authenticated P72/P115 ports has degree 28 modulo 1,000,000,007 with
leading coefficient 59132194, proving exact specialized integer degree 28.
The checker pins both graphs and port bytes, verifies the gate edit and
liveness, checks the finite port bounds and 300 signed modular controls,
samples the orientation inequalities, and computes the ray. Finite controls
do not replace the unbounded proof, calibration, or inherited endpoint.

```
python3 -I -S -B research/ordinary13-natural-cfold-forced-gamma96-degree28/check.py > /tmp/natural13-cfold-gamma96.json
cmp /tmp/natural13-cfold-gamma96.json research/ordinary13-natural-cfold-forced-gamma96-degree28/result.json
```
