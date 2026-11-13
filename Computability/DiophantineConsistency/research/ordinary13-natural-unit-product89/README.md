# Thirteen natural inputs: 89 operations, degree 99

This proposed graph has 13 nonnegative inputs, 89 live binary operations,
and exact degree 99 at the authenticated compact44 ports. It has the same
natural-zero existence as the positive-zero existence of the reviewed
[13/80/99 unit-product graph](../ordinary13-unit-product80/) whenever the
integer port `beta > 0`; the other three integer ports are arbitrary for
this local map. The inherited endpoint uses additional port/calibration
hypotheses, which are not weakened here. An [independent review](../../reviews/ordinary13-natural-unit-product89-independent/README.md)
checks the root switch, graph edit and specialized degree. There is no new Lean/iPRA theorem, PDF or byte
binding, fresh provider replay, or minimality claim.

## Graph edit and algebraic identity

Use natural inputs `n_J` through `n_gamma` in the parent's order. The parent
coordinates `f`, `r`, `y` are represented directly by their natural inputs;
each of the other ten parent coordinates is the corresponding natural input
plus one. Instead of incrementing zeta separately, compute

```
kbase = (n_eta+1) + n_zeta,
k = kbase+1,
r0 = kbase−R.
```

These are the old `k=eta+zeta` and `r0=k−R−1`. Nine added gates and the
unchanged eighty-parent graph after this cut give 89 live gates. For arbitrary
signed integer inputs and ports, the new output equals the parent output
under the displayed affine substitution. The complete DAG edit in the checker
establishes the structural part of this identity; the two `k` cuts are
elementary ring identities.

## Explicit zero transfers

Every positive parent zero maps to a natural new zero by subtracting one
from the ten shifted coordinates and keeping `f`, `r`, `y` unchanged.
Conversely, suppose the new graph has a natural zero. All the parent's
coordinates except possibly `f`, `r`, and `y` are positive. In particular,
with `b=J*beta`, `q=b+1`, `X=q*w`, `Y=q³*s`, `m=X*Y²`,
`k=eta+zeta`, and `ell=m*k`, we have `b>0`, `m>0`, `k>=2`, and `ell>0`.

The reviewed parent's four factor exclusions hold for **arbitrary integer
inputs**, so its zero gives `F0=F1=Fa=Fs=1` even at `f=0`, `r=0`, or
`y=0`. Writing `Delta=a²+4a+3 > 1`, `Q=Delta*(f²−1)`, and `Fs=1+I²−Q`,
the equation `Fs=1` rules out `f=0`: it would give `I²=−Delta<0`. The
equation `Fa=1` rules out `y=0`: it would give `Delta*(f²−1)*V²=1`.

If `r>0`, the affine identity already gives a positive parent zero. If
`r=0`, define

```
B = (q−F−alpha)*(X+K0)−F,
Z = b*(ell+k+r−k*B)−B,
Z² = b²*(1+ell*(ell+k)).
```

If `B<=0`, then `Z>=b*(ell+k)>0`, whereas
`(ell+k)² > 1+ell*(ell+k)` because `ell>0` and `k>=2`; this contradicts the
first norm equation. Thus `B>0`.

Since `b²` divides `Z²`, the elementary prime-factor (or coprime-fraction)
argument gives `b | Z`, and the definition of `Z` gives `b | B`. Let
`t=B/b>=1` and `tau=|Z|/b`; the norm equation gives

```
ell < tau < ell+k.
```

If `Z>=0`, then with `r=0` the expression for Z gives
`tau=ell+k−k*B−t <= ell−1`, a contradiction. Hence `Z<0`. Replace the
parent's coordinate `r=0` by `r'=2*tau>0`, leaving all other coordinates
unchanged. This changes `Z` by `2*b*tau=−2*Z`, so its sign reverses and its
square is preserved. The other three factors do not depend on `r`, so the
result is a positive parent zero. This is a constructive root-switch map,
not a claim that every natural zero already has `r>0`.

## Exact degree and checks

The affine substitutions do not increase the positive parent's degree-99
upper bound. The candidate's all-inputs-equal ray at the authenticated
P72/P115 ports has degree 99 modulo 1,000,000,007 with leading coefficient
663418019, proving exact specialized integer degree 99. The checker pins
both graphs and the port bytes, checks all 89 gates/inputs/ports are live,
checks the exact graph delta and 300 signed modular affine controls, and
tests finite root inequalities. Those finite tests do not prove the
unbounded root-switch argument or the inherited endpoint.

```
python3 -I -S -B research/ordinary13-natural-unit-product89/check.py > /tmp/natural13-product89.json
cmp /tmp/natural13-product89.json research/ordinary13-natural-unit-product89/result.json
```
