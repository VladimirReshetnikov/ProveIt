# Thirteen-input residue-adjusted carrier: 82 operations, degree 56

This **proposed** graph has 13 positive inputs, 82 live operations and exact
degree 56 at the authenticated compact44 ports. It applies the residue
adjustment of [`13/81`](../ordinary13-residue-first81/) directly to the
reviewed [`13/84` q-cubed unscaled parent](../ordinary13-qcube-unscale84/),
without replacing X by q*w. The positive-zero proof below uses an external
fact-level replay of the cited calibration. This packet requires independent
review and adds no Lean/iPRA theorem, PDF/JSON binding, fresh provider replay
or global minimum claim.

## Source delta and signed identity

Write `b=J*beta`, `q=b+1`, `Y=q³*s`, `m=X*Y²`, `k=eta+zeta`,
`ell=m*k`, and `C=q−F−alpha`. The parent uses

```
B = C*(X+K0*q)−F*q,
Zold = b*(ell+k+r_old−k*B)−B.
```

The new graph instead uses

```
Bprime = C*(X+K0)−F,
Znew = b*(ell+k+r_new−k*Bprime)−Bprime.
```

Both first residuals are `Z²−b²*(1+m*(m+1)*k²)`; the other three
residuals are identical. Put `D=C*K0−F`. Since `B=Bprime+b*D`, the
integer coordinate shift `r_old=r_new+(k*b+1)*D` makes `Zold=Znew`, and
`b|B` iff `b|Bprime`. This signed identity does not by itself preserve
positivity of r.

The graph deletes `K0*q` and `F*q` and retargets their consumers, reducing
84 gates to 82. The checker verifies that exact delta, topology/liveness,
160 signed root-shift controls and authenticated port bytes.

## Positive-zero maps

Assume the fixed ports satisfy the bounds used by the reviewed sign-free
decoder: `beta>=46`, `K0>=0`, `0<MC<beta`, `0<MF<2*beta`. The
authenticated compact44 ports satisfy these assumptions. For a zero of
either graph, write P for its own transport expression, B or Bprime.
The first norm yields `b|Z` and hence `b|P`. With `t=P/b` and
`tau=|Z|/b>0`, it gives

```
tau²=1+m*(m+1)*k²,
r=k*P+t−ell−k ± tau,
tau<ell+k.
```

If P were nonpositive the displayed r would be negative, so P>0. For
either definition, P>0 and `K0>=0` force `C>0` and `F+alpha<q`.

The unchanged main/strong/direct-auxiliary norms, first Pell norm,
`Y=q³*s` and positive scalar gap give the fact-level hypotheses in the
reviewed [`ordinary14-shifted-guard87-calibration`](../ordinary14-shifted-guard87-calibration/).
In particular, the `13/87` direct-auxiliary proof recovers positive
`u=y−V` from the norms; the index theorem uses `mu=q⁴` and `i_prime=i`.
The main-root orientation and rank congruence are derived from the present
carrier, rather than by applying a literal-zero wrapper requiring an old
first coordinate. The cited source theorem statements then give `X=2^R`,
while the positive-gap rank bound gives `R>=q³`; consequently `X>=q²`.
This is an external replay, not a Lean theorem for either graph.

Now `C>=1` and `F<=q−2`, so both transport expressions are positive:

```
Bprime >= q²−(q−2) > 0,
B      >= q²−(q−2)*q = 2q > 0.
```

Their b-divisibility is equivalent by `B−Bprime=b*D`. Keep all non-first
coordinates fixed. For the other graph let P be its positive transport
expression and `tP=P/b>=1`, and choose

```
r_other = k*P+tP−ell−k+tau
        = k*(P−1)+tP+(tau−ell) > 0.
```

Here `tau>ell` follows from `tau²−ell²=1+m*k²>0`. The new first
expression is `b*tau`, so its first residual vanishes; all others are
unchanged. This proves both positive-zero existence directions, possibly
switching root branches. It is not a pointwise positive-domain bijection.

## Exact degree

For fixed ports, the first, strong and direct-auxiliary residuals have degree
at most 22, 22 and 28. For the main residual write `Dstar=U*a*c+delta`,
where `deg(U*a*c)<=16` and `deg(delta)<=12`; the exact identity

```
A1=2*U*a*c*delta+delta²−U²*(1+H*c²)
```

gives `deg A1<=28`. The sum of four squares therefore has degree at most
56. The whole graph's authenticated all-inputs-equal ray modulo
1,000,000,007 has degree 56 with leading coefficient 58796952, proving
exact specialized integer degree 56. The Mersenne form is checked for the
actual port binding but is not used as a premise in the local map above.

```
python3 -I -S -B research/ordinary13-residue-first82/check.py > /tmp/residue-first82.json
cmp /tmp/residue-first82.json research/ordinary13-residue-first82/result.json
```

The finite controls do not replace independent review of the unbounded
positive-witness and source-theorem reasoning.

Independent external review is recorded in
`../../reviews/ordinary13-residue-first82-independent/`.
