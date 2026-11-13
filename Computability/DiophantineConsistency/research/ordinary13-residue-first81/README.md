# Thirteen-input residue-adjusted carrier: 81 operations, degree 60

This **proposed** graph has 13 positive inputs, 81 live operations and exact
degree 60 at the authenticated compact44 ports. It replaces the first
carrier's transport expression in the separately proposed
[`13/83` graph](../ordinary13-qcube-main83/) by a congruent expression.
The positive-zero proof below depends on a fact-level replay of the cited
compact44 calibration; this packet and its parent require independent
review. It is not a new Lean/iPRA theorem, PDF/JSON binding, fresh provider
replay or global minimum claim.

## The changed first carrier

Let `b=J*beta`, `q=b+1`, `X=q*w`, `Y=q³*s`, `m=X*Y²`,
`k=eta+zeta`, `ell=m*k`, and `C=q−F−alpha`. The parent uses

```
B = C*(X+K0*q)−F*q,
Zold = b*(ell+k+r_old−k*B)−B.
```

The proposed graph replaces B by `Bprime=C*(X+K0)−F` in that first carrier:

```
Znew = b*(ell+k+r_new−k*Bprime)−Bprime.
```

Both first residuals are `Z²−b²*(1+m*(m+1)*k²)`; all three other
residuals are unchanged. Put `D=C*K0−F`. Then `B=Bprime+b*D`, and the
integer coordinate shift `r_old=r_new+(k*b+1)*D` makes `Zold=Znew`.
In particular `b|B` iff `b|Bprime`. The shift need not preserve positivity;
the existence proof below chooses appropriate positive root branches instead.

The graph deletes `K0*q` and `F*q` and retargets their two consumers,
reducing the live count from 83 to 81. The checker verifies this exact graph
delta, 160 signed root-shift identities and all input/port/gate liveness.

## Shared norm and calibration facts

For either carrier, a positive zero implies `b|Z` and hence divisibility by
b of its transport expression. If that expression were nonpositive, the
positive first coordinate and `tau<ell+k` would be incompatible: indeed,
with `t=transport/b` and `tau=|Z|/b>0`,

```
tau²=1+m*(m+1)*k²,
r=k*transport+t−ell−k ± tau,
(ell+k)²−tau²=ell*k+k²−1>0.
```

Thus the parent has `B>0` and the new graph has `Bprime>0`. At the
authenticated ports beta is positive and `K0>=0`; either positivity implies
`C>0` and `F+alpha<q`.

The first Pell norm, the unchanged main/strong/direct-auxiliary norms,
`Y=q³*s`, `C>0` and the authenticated scalar bounds supply the **fact-level**
inputs to the reviewed sign-free decoder in
[`ordinary14-shifted-guard87-calibration`](../ordinary14-shifted-guard87-calibration/)
and its modified-main-carrier replay in
[`ordinary14-qcube84-probe`](../ordinary14-qcube84-probe/). In particular,
the direct-y auxiliary coordinate recovers the needed positive u by the
reviewed `|V|>1` argument; the index theorem uses `mu=q⁴` and `i_prime=i`.
The positive main root and factor-three cancellation are obtained from the
main norm, not from the old first coordinate. The replay concludes
`X=2^R` and the positive-gap rank bound `R>=q³`, so `X>=q²`. This is an
external application/replay of existing source theorem statements; it is not
a compiled client of the modified graph, nor a direct application of the old
literal-zero wrappers.

From `C>=1`, `F<=q−2`, `K0>=0` and `X>=q²`, both expressions are positive:

```
Bprime = C*(X+K0)−F >= q²−(q−2) > 0,
B      = C*(X+K0*q)−F*q >= q²−(q−2)*q = 2q > 0.
```

The relevant b-divisibility then transfers to the other expression by
`B−Bprime=b*D`. These facts do not assume that the other graph has a zero.

## Positive witnesses in both directions

Take a positive zero of either graph. Keep J, F, alpha, w, s and the other
non-first coordinates fixed. Its first norm supplies `tau>0` as above. The
shared calibration facts show that the other carrier's transport expression
P is a **positive** integer divisible by b; let `tP=P/b>=1`. Choose the
other graph's first coordinate

```
r_other = k*P+tP−ell−k+tau
        = k*(P−1)+tP+(tau−ell) > 0.
```

The inequality uses `tau>ell`, immediate from
`tau²−ell²=1+m*k²>0`. Its first expression is then `b*tau`, so its first
residual vanishes. The remaining residuals are independent of the first
coordinate and unchanged. This gives positive-zero existence in **both**
directions; it may switch root branches and is not a pointwise positive-domain
bijection. The actual-port source/calibration dependencies are essential to
the displayed proof.

## Degree

The first residual has degree at most 24. The direct-auxiliary and strong
residuals have degree at most 30 and 22. For the unchanged main residual,
write `Dstar=U*a*c+delta` with `deg(U*a*c)<=17` and `deg(delta)<=13`;
the cancellation

```
A1=2*U*a*c*delta+delta²−U²*(1+H*c²)
```

gives `deg A1<=30`. Therefore the sum of four squares has degree at most 60.
At the authenticated P72/P115 ports, its all-inputs-equal ray modulo
1,000,000,007 has degree 60 and leading coefficient 619528110, proving exact
specialized integer degree 60. The checker verifies the Mersenne form and
the bounds `beta>=46`, `K0>=0`, `0<MC<beta`, `0<MF<2beta`.

```
python3 -I -S -B research/ordinary13-residue-first81/check.py > /tmp/residue-first81.json
cmp /tmp/residue-first81.json research/ordinary13-residue-first81/result.json
```

Finite substitution controls are not a substitute for independent review
of the positive-witness and source-theorem reasoning above.

Independent mathematical review is recorded in
`../../reviews/ordinary13-residue-first81-math-independent/`.
