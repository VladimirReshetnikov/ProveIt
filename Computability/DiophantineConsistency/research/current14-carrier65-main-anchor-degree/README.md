# A structural limit on direct main-anchor aliases

This is an exact algebraic observation about possible **direct aliases**, not
an operation lower bound. It does not exhibit a smaller equation, prove a
Lean theorem, or bind any PDF. It covers the same 37 preaggregation
gamma-free nodes used in the reviewed main-anchor sharing screen.

Write `D=main_root=D0+gamma*H`, where `H=4*a+3` and `D0=X+a*c`. The
quantities `D0,H,Delta,c` are gamma-free, and `H` is a nonzero polynomial.
The main anchor is

```
Q = N1 = D² − Delta*c².
```

Take any gamma-free polynomial `t` and any nonzero integer polynomial `A`
in the original inputs, including possibly gamma. In the polynomial ring
with the four fixed ports specialized,

```
deg_gamma(t + A*(Q−1)) = deg_gamma(A)+2 >= 2.
```

Indeed the gamma-leading coefficient of `Q−1` is `H²`, and the coefficient
ring is an integral domain. Consequently such a shear cannot be identical
to a gamma-free gate or to `gammaH` or `main_root`, which are linear in
gamma. This applies to arbitrary polynomial coefficients `A`, not merely
the multiplication shear previously screened.

There are only two preaggregation gamma-dependent gates of degree two:
`main_square=D²` and `N1=Q`. Comparing gamma-leading coefficients and then
constant terms gives the exact exceptional cases

```
t + A*(Q−1) = Q    iff A=1 and t=1,
t + A*(Q−1) = D²   iff A=1 and t=Delta*c²+1.
```

The checker pins the maintained graph and actual port payloads, verifies the
four gamma-dependent preaggregation nodes and all 37 selected targets, and
finds a nonzero modular residue witness for each target's difference from
both exceptional gamma-free expressions. Thus none of these 37 shears can
directly alias *any* original preaggregation node, for any nonzero polynomial
coefficient A. A modular nonzero is only used to disprove a polynomial
identity; it does not certify a candidate.

This argument does **not** rule out reuse of final aggregation nodes,
combinations of multiple shears, alternative anchors, non-polynomial
coefficients, cheaper multi-gate expressions, or entirely different
zero-preserving transformations. It also does not assert that every formal
shear admits an acyclic implementation or preserves the equation; the
reviewed unit-anchor proof supplies zero equivalence only when its separate
hypotheses hold.

```
python3 -I -S -B research/current14-carrier65-main-anchor-degree/check.py > /tmp/main-anchor-degree.json
cmp /tmp/main-anchor-degree.json research/current14-carrier65-main-anchor-degree/result.json
```

Independent external review is recorded in
`../../reviews/current14-carrier65-main-anchor-degree-independent/`.
