# Forced gamma: 13 natural inputs, 87 operations, degree 99

This proposed graph deletes `gamma=n_gamma+1` from the proposed
[13/88/99 natural unit-product graph](../ordinary13-natural-unit-product88/)
and uses `n_gamma` directly. It has 13 nonnegative inputs, 87 live binary
operations, and exact degree 99 at the authenticated compact44 ports. The
zero-existence maps below use integer ports satisfying `beta>=46`, `K0>=0`,
`0<MC<beta`, and `0<MF<2*beta`, plus the cited rank-window theorem and
elementary Pell descent. These port bounds hold for the authenticated
compact44 values. The external proof has an [independent review](../../reviews/ordinary13-natural-forced-gamma87-independent/README.md)
of its rank, Pell and graph arguments; it is not a Lean/iPRA theorem, PDF or byte binding,
fresh provider replay, or global minimum claim.

## Graph and zero maps

The only graph edit deletes the gamma increment and retargets its consumer.
Over arbitrary signed integers, the new output at `gamma=g` equals the
88 output at `n_gamma=g−1`, with the other inputs unchanged. Any 88 natural
zero therefore maps to an 87 zero by incrementing `n_gamma`. Conversely,
the following argument proves that every natural 87 zero has `gamma>0`;
subtract one to obtain a natural 88 zero. These maps are inverse on zeros.

## Consequences of an 87 zero

The four-unit argument of the underlying 13/80 graph is valid for arbitrary
integer inputs and ports. Thus an 87 zero gives all four factors +1, and
the four norm residual equations hold even when `gamma=0`. The unchanged
forced-J argument of the 88 packet uses the first residual, `F,alpha,w>0`,
and `K0>=0`, but does not use gamma positivity; it gives `J>0`. Hence

```
b=J*beta>0, q=b+1>=2, X=q*w>=q, Y=q³*s>=q³,
m=X*Y²>=q⁷, k=eta+zeta>=2, ell=m*k.
```

Write `B=(q−F−alpha)*(X+K0)−F`. If `B<=0`, the first expression
`Z=b*(ell+k+r−k*B)−B` is at least `b*(ell+k)` even with natural `r=0`.
But the first norm says `Z²=b²*(1+ell*(ell+k))`, and the right-hand
square root is strictly smaller than `ell+k` for `ell>0`, `k>=2`. Thus
`B>0`, and since `X+K0>0` and `F>0`, this forces
`C=q−F−alpha>0`, or equivalently `F+alpha<q`.

Let `a=XY+Y`, `c=eta+Y*k`, `H=3+4*a`, `U=Y*q²`,
`Delta=(a+2)²−1`, and

```
R=(alpha+(q−F)*b)*(q²−1)+J*(MC+MF*q).
```

All terms in `R` are nonnegative. The assumptions match
`ArithmeticAdaptiveRankWindow2011.scalar_rank_window`, which gives
`R+q³+q+1<=q⁴`, so `R+1<q⁴`. This is a fact-level application to the
ordinary natural numbers; the checker does not elaborate or replay the
Lean theorem.

The main norm gives an integer `d_abs=|Dstar|/U` satisfying
`d_abs²=1+Delta*c²`: `U>0` and `U² | Dstar²` imply `U | Dstar` by the
elementary prime-factor argument. If `k=2`, then `eta=zeta=1` and
`c=2*Y+1`. Since `1<c<2*(a+2)`, the quantity `1+Delta*c²` lies strictly
between `((a+2)*c−1)²` and `((a+2)*c)²`, contradiction. Thus `k>2`.

The first norm similarly yields a natural `tau=|Z|/b` with
`tau²−m*(m+1)*k²=1`. The elementary descent in the independently reviewed
[`folded-root86-negated-positive-bt`](../ordinary13-folded-root86-negated-positive-bt/)
packet, applied only to this Pell equation with `m>=1` and `k>2`, gives
`k>=8*m+4`. It follows that

```
k >= 8*q⁷+4 > q⁴ > R+1,
c=eta+Y*k > X.
```

## Gamma cannot vanish

Suppose `gamma=0`. The main expression is

```
Dstar=U*(X+a*c)+H*(R+1−k).
```

It is positive, even without assuming gamma positive. Indeed, `c>Y*k`,
`R>=0`, and `U*a*Y=Y²*q²*a>H` because `q>=2`, `Y>=q³`, and `a>=1`.
Therefore `U*a*c>H*k` and the positive part of Dstar exceeds the magnitude
of the possible negative term. Set `d=Dstar/U>0` using the divisibility
above. Since

```
d²−((a+1)*c)² = (2*a+2)*c²+1 > 0,
```

we have `d>(a+1)*c>X+a*c`, using `c>X`. Rearranging the Dstar formula
then gives

```
0 < U*(d−X−a*c) = H*(R+1−k) < 0,
```

a contradiction. Consequently `gamma>0`, completing the stated zero maps.
The argument does not use a positive-gamma premise at any step.

## Count and degree

The single deletion leaves 87 live binary gates, all 13 inputs and four
ports. Affine substitution preserves the 88 parent's degree-99 upper
bound. At the authenticated P72/P115 ports the all-inputs-equal ray modulo
1,000,000,007 has degree 99 and leading coefficient 663418019, proving exact
specialized integer degree 99. The checker pins both graphs and port
bytes, verifies the gate edit/liveness, tests 300 signed modular identities,
checks the finite port bounds, samples the displayed orientation
inequalities, and computes the ray. Finite tests do not replace the
unbounded rank/Pell/positivity proof or prove the inherited endpoint.

```
python3 -I -S -B research/ordinary13-natural-forced-gamma87/check.py > /tmp/natural13-gamma87.json
cmp /tmp/natural13-gamma87.json research/ordinary13-natural-forced-gamma87/result.json
```
