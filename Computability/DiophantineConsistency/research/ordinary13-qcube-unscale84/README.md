# Thirteen-input q-cubed unscaled carrier: 84 operations, degree 56

This **proposed** graph has 13 strictly positive inputs, 84 live arithmetic
operations and exact degree 56 at the authenticated compact44 ports. For
arbitrary integer ports with `beta>0`, its positive-zero existence is
equivalent to that of the reviewed 13-input
[`87/36` direct-auxiliary parent](../ordinary13-aux-root87-36/). The local
proof below and its graph/degree checks are submitted for independent review.
No new Lean/iPRA theorem, JSON/PDF binding, provider replay or global minimum
is claimed. The parent's source and endpoint qualifications are inherited.

## Unscale the first carrier

Put `b=J*beta`, `q=b+1`, `m=X*Y²`, `k=eta+zeta`, `ell=m*k` and
`Bt=(q−F−alpha)*(X+K0*q)−F*q`. The old first expression and residual are

```
Zold = q³*b*(ell+k+r_old−k*Bt) + Y*b − q³*Bt,
Aold = Zold² − (q³*b)²*(1+ell*(ell+k)).
```

Replace positive input `Y` by positive input `s`, define `Y=q³*s`, and
interpret the new positive first-coordinate input `r` as `r_old+s`. Define

```
Z = b*(ell+k+r−k*Bt)−Bt,
A = Z²−b²*(1+ell*(ell+k)).
```

For every integer assignment related by `r_old=r−s`, the exact identities
`Zold=q³*Z` and `Aold=q⁶*A` hold; the other three residuals are unchanged.
The first residual is one member of a sum of four integer squares. Since
`beta,J>0`, both q and b are positive, so multiplication by q⁶ does not
change vanishing.

## Positive witnesses in both directions

From an old positive zero, `M=q³*b>0` and the first norm imply `M|Zold`
(e.g. by integer prime valuations). Reducing `Zold` modulo q³ gives
`q³|Y`, because gcd(q,b)=1. Thus `s=Y/q³>0`, and `r=r_old+s>0`. The
displayed identities give a new positive zero.

Conversely, take a positive new zero. Its first norm implies `b|Z`, hence
`b|Bt`; put `t=Bt/b` and `tau=|Z|/b>0`. Then

```
tau² = 1+m*(m+1)*k²,
r = k*Bt+t−ell−k ± tau.
```

The norm also gives `tau<ell+k`, because
`(ell+k)²−tau²=ell*k+k²−1>0`. If `Bt<=0`, then `t<=0` and either
displayed value of r is negative, contradicting positivity. Thus `Bt>0`
and `t>=1`.

The unchanged main norm excludes `k=2` by the consecutive-square argument in
[`ordinary13-folded-root86-negated-positive-bt`](../ordinary13-folded-root86-negated-positive-bt/).
The first Pell descent there gives `k>=8m+4` and `tau−ell>k/4>2m`.
Since `m=X*Y²>=Y>=s`, choose the positive old first coordinate

```
r_old = k*Bt−ell−k−s+t+tau
      = k*(Bt−1)+t−s+(tau−ell) > 0.
```

Retain all other coordinates and the old Y. Its old first expression equals
`q³*b*tau`, so its first residual vanishes; the other three residuals are
unchanged. This construction may switch first-root branches and therefore
proves existence equivalence, not a pointwise positive-domain bijection.
The argument uses no sign assumption on K0.

## Gate count and exact degree

The source delta removes the old `M=q³*b`, `Y*b`, their sum and `q³*Bt`
gates, adds `Y=q³*s`, and retargets three first-carrier gates. Thus there are
`87−4+1=84` live gates; all 13 inputs and all four fixed leaves remain live.

With the fixed numerals treated as constants, the source has degree bounds
`deg Y<=4`, `deg U<=6`, `deg a<=5`, `deg c<=5`, `deg H<=5`,
`deg ell<=10`, `deg Bt<=2` and `deg Z<=11`. The first residual has degree
at most 22, the strong residual at most 22, and the direct auxiliary
residual at most 28. The naive bound for the main residual is 32, but write

```
Dstar = U*a*c + delta,  delta = U*X + H*shift,
A1 = 2*U*a*c*delta + delta² − U²*(1+H*c²).
```

Here `deg(U*a*c)<=16`, `deg(delta)<=12`, and
`deg(U²*(1+H*c²))<=27`, so `deg A1<=28`. The four-square output therefore
has degree at most 56. A direct all-inputs-equal ray at the authenticated
P72/P115 ports modulo 1,000,000,007 has degree 56 and leading coefficient
58796952, proving exact specialized integer degree 56.

The checker pins both complete graphs and both port bindings, verifies source
delta, topology and liveness, and checks the substitution identity on 160
signed assignments. These finite controls do not replace the unbounded
positive-witness proof or degree bound.

```
python3 -I -S -B research/ordinary13-qcube-unscale84/check.py > /tmp/qcube-unscale84.json
cmp /tmp/qcube-unscale84.json research/ordinary13-qcube-unscale84/result.json
```

Independent external review is recorded in
`../../reviews/ordinary13-qcube-unscale84-independent/`.
