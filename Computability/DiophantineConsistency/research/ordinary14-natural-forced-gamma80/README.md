# Forced gamma: 14 natural inputs, 80 operations, degree 107

This proposed graph deletes `gamma=n_gamma+1` from the proposed
[14/81/107 natural graph](../ordinary14-natural-forcedj81/) and uses
`n_gamma` directly. It has 14 nonnegative inputs, 80 live binary operations
and exact degree 107 at the authenticated compact44 ports. The zero maps
below use integer ports with `beta>=46`, `K0>0`, `0<MC<beta`, and
`0<MF<2*beta`, the rank-window theorem, and elementary Pell descent. The
authenticated ports satisfy these bounds. The external argument has an
[independent review](../../reviews/ordinary14-natural-forced-gamma80-independent/README.md), but is not a Lean/iPRA theorem, PDF or
byte binding, fresh provider replay, or minimality claim.

## Graph edit and zero maps

The only graph edit deletes the gamma increment and retargets its consumer.
For arbitrary signed integers, the 80 output at `gamma=g` equals the 81
output at `n_gamma=g−1`, with the other coordinates unchanged. An 81 natural
zero maps to an 80 zero by incrementing `n_gamma`. Conversely, the proof
below forces `gamma>0` at every natural 80 zero; subtracting one gives an
81 natural zero. The maps are inverse on zeros.

## Unit, rank and Pell consequences

At an 80 zero the five integer factors multiply to one. The existing
strict-K0 guard-unit argument works with arbitrary gamma, so `J>0`. Hence

```
b=J*beta>0, q=b+1>=2, X=q*w>=q, Y=q³*s>=q³,
m=X*Y²>=q⁷, k=eta+zeta>=2, ell=m*k.
```

The first factor cannot be −1 by the reviewed negative-Pell exclusion for
`m>=2`; the main, auxiliary and strong factors cannot be −1 modulo 4.
Thus all five factors are +1, independently of gamma's sign. The guard
equation gives `C*(X+K0)−F=b*n_h>=0`. With `F>0`, `X+K0>0`, this
forces `C=q−F−alpha>0`, or `F+alpha<q`.

Let

```
a=XY+Y, c=eta+Y*k, H=3+4*a, U=Y*q²,
Delta=(a+2)²−1,
R=(alpha+(q−F)*b)*(q²−1)+J*(MC+MF*q).
```

All terms in R are nonnegative. The port assumptions and positive input
conditions match `ArithmeticAdaptiveRankWindow2011.scalar_rank_window`,
which yields `R+q³+q+1<=q⁴`, so `R+1<q⁴`. The first and main units give

```
r²−m*(m+1)*k²=1,
Dstar²=U²*(1+Delta*c²).
```

Since `U>0`, the second norm gives `U | Dstar`, so
`d_abs=|Dstar|/U` is an integer with `d_abs²=1+Delta*c²`. If `k=2`, then
`eta=zeta=1` and `c=2Y+1`; because `1<c<2*(a+2)`, this quantity lies
strictly between `((a+2)*c−1)²` and `((a+2)*c)²`, contradiction. Thus
`k>2`. The elementary descent in the independently reviewed
[`folded-root86-negated-positive-bt`](../ordinary13-folded-root86-negated-positive-bt/)
packet, applied to the first Pell equation with `m>=1` and `k>2`, yields
`k>=8*m+4`. Consequently `k>=8*q⁷+4>q⁴>R+1` and
`c=eta+Y*k>X`.

## Gamma cannot vanish

If `gamma=0`, the main expression is

```
Dstar=U*(X+a*c)+H*(R+1−k).
```

It is positive: `c>Y*k`, `R>=0`, and `U*a*Y=Y²*q²*a>H` for
`q>=2`, `Y>=q³`, `a>=1`, so `U*a*c>H*k`. Thus the signed quotient
`d=Dstar/U` is positive. Its norm implies

```
d²−((a+1)*c)²=(2*a+2)*c²+1>0,
```

so `d>(a+1)*c>X+a*c`, using `c>X`. Rearranging Dstar gives the
contradiction

```
0 < U*(d−X−a*c)=H*(R+1−k)<0.
```

Therefore `gamma>0`. No positive-gamma premise is used in the argument.

## Count and degree

All 80 binary gates, 14 inputs and four ports are live. The affine edit
preserves the parent's degree-107 upper bound. The all-inputs-equal ray at
authenticated P72/P115 ports has degree 107 modulo 1,000,000,007, leading
coefficient 419359493, proving exact specialized integer degree 107. The
checker pins both graphs and port bytes, verifies the gate edit/liveness,
checks the finite port bounds and 300 signed modular controls, samples the
orientation inequalities and computes the degree ray. Finite controls do
not replace the unbounded proof or inherited endpoint.

```
python3 -I -S -B research/ordinary14-natural-forced-gamma80/check.py > /tmp/natural14-gamma80.json
cmp /tmp/natural14-gamma80.json research/ordinary14-natural-forced-gamma80/result.json
```
