# Forced gamma and shifted Pell root: 14 natural inputs, 81 operations, degree 97

This proposed graph deletes `gamma=n_gamma+1` from the proposed
[14/82/97 forced-J shifted-Pell graph](../ordinary14-natural-forcedj82-degree97/).
It has 14 nonnegative inputs, 81 live binary operations and exact degree 97
at the authenticated compact44 ports. Its natural-zero existence agrees with
that parent under `beta>=46`, `K0>0`, `0<MC<beta`, and `0<MF<2*beta`,
using the same rank-window theorem and elementary Pell descent as the
separate [14/80/107 forced-gamma proof](../ordinary14-natural-forced-gamma80/).
The actual authenticated ports satisfy these bounds. Both packets have
independent reviews; see the [shifted-root review](../../reviews/ordinary14-natural-forced-gamma81-degree97-independent/README.md).
This is external mathematics, not a Lean/iPRA theorem,
PDF or byte binding, fresh provider replay, or minimum claim.

## Coordinate maps and forced gamma

Delete the gamma increment and use the input directly. The candidate output
at `gamma=g` equals the parent output at `n_gamma=g−1` for every signed
integer valuation and ports. A parent zero maps to the candidate by
incrementing `n_gamma`; a candidate zero maps back by subtracting one once
`gamma>0` is established. These maps are inverse on zeros.

At a candidate zero, the strict-K0 guard-unit argument gives `J>0`. All
four restricted factors are then +1: the main, auxiliary and strong
factors exclude −1 modulo 4, while the shifted first factor is

```
F0=t²+ell*(2*t−k)=(ell+t)²−m*(m+1)*k²,
m=X*Y²>=2, ell=m*k, t=n_t>=0,
```

and the reviewed negative-Pell lemma excludes −1. The guard is therefore
also +1, giving `C*(X+K0)−F=b*n_h>=0`, so `C>0`. Its first unit gives the
ordinary positive-root Pell equation

```
(ell+t)²−m*(m+1)*k²=1.
```

Every remaining hypothesis of the full forced-gamma proof in the linked
80/107 packet is unchanged: `q>=2`, `X>=q`, `Y>=q³`, `eta,zeta>0`,
the same main unit and rank expression, and the stated port bounds. That
argument gives `k>=8m+4>R+1`, `Dstar>0` if `gamma=0`, and then
`0<U*(d−X−a*c)=H*(R+1−k)<0`, contradiction. Hence `gamma>0`.

## Count and degree

All 81 binary gates, 14 inputs and four ports are live. The affine edit
preserves the parent's degree-97 upper bound. At the authenticated P72/P115
ports the ray with `n_t=2*x` and all other inputs equal to `x` has degree
97 modulo 1,000,000,007 and leading coefficient 979034495, proving exact
specialized integer degree 97. The checker pins both graphs and port bytes,
checks the gate edit/liveness, actual port bounds and 300 signed modular
controls, samples the orientation inequalities and computes the ray. The
finite checks do not replace the unbounded gamma argument or inherited
endpoint. Compared with the proposed 80/107 graph, this uses one more gate
and has degree ten lower; neither dominates the other in those two measures.

```
python3 -I -S -B research/ordinary14-natural-forced-gamma81-degree97/check.py > /tmp/natural14-gamma81-97.json
cmp /tmp/natural14-gamma81-97.json research/ordinary14-natural-forced-gamma81-degree97/result.json
```
