# C-fold with direct auxiliary root: 13 inputs, 87 operations, degree 36

This proposed graph has **13 strictly positive inputs, 87 live operations
and exact degree 36** at the authenticated compact44 ports. It applies the
positive auxiliary-root substitution to the reviewed 13-input 88/28 C-fold.
The local positive-zero comparison requires only `beta>0`; the C-fold's
comparison to its parent additionally inherits the documented compact44
sign-free calibration. This is external mathematics submitted for review,
not a new Lean/iPRA theorem, PDF/JSON binding, provider replay or minimum.

Let

```
V=f²*(T*c−R)−c, Q=Delta*(f²−1), I=i*c², y=V+u.
```

The 88/28 parent takes positive u and computes
`Fa=y²−Q*u*(y+V)`. The new graph takes positive y directly and computes
`Fa=y²−Q*(y²−V²)`. Their auxiliary expressions agree whenever `y=V+u`,
by `u*(y+V)=y²−V²`. The other three squared residuals are unchanged.

## Positive-coordinate maps

At a zero, all four squares vanish. The first and main norm equations give
`k>2` by the reviewed consecutive-square exclusion and then
`k>=8XY²+4` by the reviewed elementary Pell descent. With
`c=eta+Y*k` and `Delta=(Y*(X+1)+2)²−1`, positivity gives

```
c>8XY³,    Delta<16X²Y²<c³.
```

The strong residual gives `Delta*(f²−1)=i²*c⁴>=c⁴`, hence
`f²>c+1`. Since `f²|(V+c)` and `c−1,c,c+1` are positive and below f²,
`V` cannot be −1, 0 or 1. Thus `|V|>1`. The same strong residual gives
`Q=(ic²)²>1`. At an auxiliary zero,

```
(Q−1)*(y²−V²)=V²−1>0,
```

so `|y|>|V|`. In an old positive zero, `y=V+u>V`; it cannot be
nonpositive and is a valid positive new input. In a new positive zero,
`u=y−V>0` is a valid old input. Both maps keep all other inputs fixed and
preserve every residual. They do not assume a sign for V, an old zero in the
reverse direction, or the compact44 calibration.

## Count and degree

The literal graph deletes `y=V+u`, `y+V` and their product, and adds V²
and `y²−V²`, saving one operation: `88−3+2=87`. All 13 inputs and four
fixed leaves are live. The checker reconstructs the complete source delta,
checks unique names/topology/liveness, runs 100 signed substitution controls,
and authenticates P72/P115 compact44 payload bytes.

At fixed ports, `deg(Delta)<=4`, `deg(Q)<=6`, `deg(V)<=6`, so the new
auxiliary residual has degree at most 18. The first residual is at most 14,
the main at most 13 and the strong at most 10; the sum of squares is at most
degree 36. A direct all-inputs-equal ray at the authenticated ports has degree
36 with leader 351467226 modulo 1000000007, proving exact specialized degree
36.

At the same 13-input, 87-operation count this lowers the degree of the named
87/51 free-J record to 36. The 13-input 88/28 C-fold trades one more operation
for lower degree. These are comparisons to named records, not global
optimality or an internal proof about the displayed 65/150 PDF equation.

```
python3 -I -S -B research/ordinary13-cfold-aux87/check.py > /tmp/cfold-aux87.json
cmp /tmp/cfold-aux87.json research/ordinary13-cfold-aux87/result.json
```

Finite controls do not replace the unbounded Pell/root argument or the
degree upper bound. The parent source/provider and endpoint qualifications
remain in force.

Independent external review is recorded in
`../../reviews/ordinary13-cfold-aux87-independent/`.
