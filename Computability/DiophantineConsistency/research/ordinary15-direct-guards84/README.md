# Two explicit quotients: 15 inputs, 84 operations, degree 36

This proposed graph has **15 strictly positive inputs, 84 live operations and
exact degree 36** at the authenticated compact44 ports. It replaces the
scaled first carrier of `../ordinary13-aux-root87-36/` with a direct positive
Pell root and two explicit positive quotient guards. Its positive-zero
existence is equivalent to that parent's for arbitrary integer ports with
`beta>0`, subject to independent review. It adds no Lean/iPRA theorem,
PDF/JSON binding, provider replay or global optimality result.

Put

```
b=J*beta, q=b+1, M=q³*b, m=X*Y²,
k=eta+zeta, ell=m*k, C=q−F−alpha,
Bt=C*(X+K0*q)−F*q.
```

The parent has first expression

```
Z=M*(ell+k+r_old−k*Bt)+Y*b−q³*Bt,
```

with residual `Z²−M²*(1+ell*(ell+k))`. The new graph replaces it by
`tau²−(1+ell*(ell+k))`, where tau is a positive input, and adds two
positive inputs s,t with squared guards

```
(Y−q³*s)²,     (Bt−b*t)².
```

All other three parent residuals and the thirteen original input roles are
retained, with tau replacing r_old.

## Positive-zero maps

From a positive parent zero, the first norm and M>0 give `M|Z`, then
`q³|Y` and `b|Bt`. Moreover Bt>0: otherwise its literal Z would exceed
`M*(ell+k)`, contrary to the first norm. Set `s=Y/q³>0`, `t=Bt/b>0`,
and `tau=|Z|/M>0`. The first and both guard residuals vanish, and the other
three are unchanged, so this is a positive new zero. The proof uses no
assumption on the sign of K0.

Conversely, in a positive new zero the guards give `Y=q³*s` and
`Bt=b*t>0`. The main norm excludes k=2, and the elementary Pell descent in
`../ordinary13-folded-root86-negated-positive-bt/` gives
`tau−ell>k/4>2s`. Thus

```
r_old=k*Bt−ell−k−s+t+tau
     =k*(Bt−1)+t−s+(tau−ell) > 0.
```

Substitution gives `Z=M*tau`. All other residuals agree with the parent, so
this r_old constructs a positive parent zero. These maps use only beta>0,
the positivity of inputs, integer square/divisibility arguments and the
reviewed Pell descent; compact44 calibration is not needed for this local
comparison. The parent's endpoint qualifications remain inherited.

## Count and degree

The checker reconstructs the full graph delta: eleven old scaled-root gates
are deleted, the remaining first square/subtraction are retargeted, and two
four-gate squared-guard additions are appended: `87−11+8=84`. All 84 gates,
15 inputs and four fixed leaves are live. The checker authenticates both
P72/P115 port bindings and tests 100 signed controls of the exact root
identity, including the guard-error terms.

With X and Y both inputs of degree 1, the direct first residual has degree at
most 8, the main residual at most 13 by the reviewed cancellation, the direct
auxiliary residual at most 18, and the strong residual at most 10. The Y and
Bt guards have degrees at most 4 and 2. Hence the complete sum of squares has
degree at most 36. The full all-inputs-equal ray at authenticated compact44
ports has degree 36 with leader 351467226 modulo 1000000007, proving exact
specialized integer degree 36.

This trades two more inputs for three fewer operations at the same degree
versus the named 13-input 87/36 direct-auxiliary form. The 14-input 78/60
form has fewer inputs and operations but higher degree. These are named
numerical comparisons, not claims of a global frontier or of an internal
proof about the displayed PDF equation.

```
python3 -I -S -B research/ordinary15-direct-guards84/check.py > /tmp/direct-guards84.json
cmp /tmp/direct-guards84.json research/ordinary15-direct-guards84/result.json
```

The finite checker does not replace the unbounded root and positivity proof.

Independent external review is recorded in
`../../reviews/ordinary15-direct-guards84-independent/`.
