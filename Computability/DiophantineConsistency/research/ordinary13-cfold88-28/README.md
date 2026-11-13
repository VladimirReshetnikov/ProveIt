# A C-weighted fold with 13 positive inputs, 88 operations and degree 28

This graph changes the reviewed free-J 88/30 parent at one multiplication:
replace the first-root term `k*Bt` by `k*C`. It has **13 strictly positive
inputs, 88 live operations and exact degree 28** at the authenticated
compact44 ports. The argument below proposes positive-zero existence
equivalence with that parent. It is submitted for independent review and
uses the independently reviewed sign-free calibration facts as external
mathematics. It adds no Lean or iPRA theorem, PDF/JSON binding theorem,
provider-ancestry replay or global minimality result.

Write

```
b=J*beta, q=b+1, C=q−F−alpha, Bt=C*(X+K0*q)−F*q,
M=q³*b, m=X*Y², k=eta+zeta, ell=m*k.
```

The parent and candidate first expressions are respectively

```
Z_old = M*(ell+k+r_old−k*Bt)+Y*b−q³*Bt,
Z_new = M*(ell+k+rho−k*C)+Y*b−q³*Bt.
```

All other residuals agree. Over arbitrary integers the coordinate substitution
`rho=r_old−k*Bt+k*C` makes their complete four-square outputs equal. The
checker pins this literal single-row graph change and exercises the identity
on finite integer controls. Positivity requires the existence proof below.

## Hypotheses

For the actual compact44 ports, the checker authenticates both P72 and P115
bindings and verifies

```
beta>=46, K0>=0, 0<MC<beta, 0<MF<2*beta.
```

The two implications use these conditions and the sign-free fact-level
calibration replay in `../ordinary14-shifted-guard87-calibration/`: from
positive inputs, `C>0`, `q³|Y`, and the four vanishing norm residuals, the
replay gives `X=2^R>=q²` at these ports. Its guard was used only to derive
C>0, not in the subsequent calibration. This is an external application of
the cited source theorems in the standard naturals, not a new modified-graph
Lean result.

## Candidate to parent

Suppose the candidate has a positive zero. If `C<=0`, then `Bt<0` and

```
Z_new > M*(ell+k).
```

But its first norm gives `Z_new²=M²*(1+ell*(ell+k))`, while
`(ell+k)²−(1+ell*(ell+k))=ell*k+k²−1>0`. This contradiction proves C>0.
The first norm gives `q³|Y` and `b|Bt` by integer square divisibility and
`gcd(q,b)=1`. All four norm residuals vanish, so the cited sign-free
calibration gives `X>=q²`. Since `C>=1` and `F<=q−2`,

```
Bt−C=C*(X+K0*q−1)−F*q >= 2*q−1 > 0.
```

Thus `r_old=rho+k*(Bt−C)` is a positive integer, and the displayed coordinate
substitution makes all parent residuals vanish.

## Parent to candidate

Take a positive parent zero. The reviewed first-norm arguments in
`../ordinary13-folded-root86-negated-positive-bt/` and
`../ordinary13-folded-root86-negated-forward/` give `Bt>0`, `q³|Y`,
`b|Bt`, and positive integers `s=Y/q³`, `t=Bt/b` and tau with

```
tau²=1+m*(m+1)*k²,    tau−ell>k/4>2*s.
```

If necessary switch to the +tau first root. Its parent coordinate is

```
r_plus=k*Bt−ell−k−s+t+tau
      =k*(Bt−1)+t−s+(tau−ell) > 0.
```

All other residuals are independent of this coordinate. Since Bt>0 implies
C>0, choose

```
rho=r_plus−k*Bt+k*C
   =(C−1)*k+(tau−ell)−s+t > 0.
```

The candidate Z is the same as the parent +tau Z, and all residuals vanish.
The argument proves positive-zero **existence** equivalence, not positive
pointwise equivalence under the unswitched first-root coordinate.

## Exact degree

Write `Z_new=M*ell+delta`, with
`delta=M*(k+rho−C*k)+Y*b−q³*Bt`. The source degrees give
`deg(M*ell)<=8` and `deg(delta)<=6`. Therefore

```
A0=2*(M*ell)*delta+delta²−M²*(1+ell*k)
```

has degree at most 14. The other three residual degrees are at most 13, 13
and 10 by the parent/signed-fold cancellation arguments, so the sum of four
squares has degree at most 28. A direct all-inputs-equal ray over the
authenticated actual ports has degree 28 and nonzero leading coefficient
59132194 modulo 1000000007, proving exact specialized integer degree 28.

At equal 13-variable and 88-operation count, this lowers the degree of the
named 88/30 free-J graph. The separately reviewed 14-variable 87/26 graph has
fewer operations and lower degree but one more input; these numerical
comparisons do not establish a global frontier.

```
python3 -I -S -B research/ordinary13-cfold88-28/check.py > /tmp/cfold88.json
cmp /tmp/cfold88.json research/ordinary13-cfold88-28/result.json
```

The finite checker does not replace the unbounded positive-zero proof.

Independent external review is recorded in
`../../reviews/ordinary13-cfold88-28-independent/`.
