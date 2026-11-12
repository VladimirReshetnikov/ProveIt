# Independent review: 13-input C-fold with direct auxiliary root

**PASS, external integer mathematics.** The frozen author packet
`../../research/ordinary13-cfold-aux87/` is positive-zero existence equivalent
to its reviewed 88/28 C-fold parent at every integer port valuation with
beta>0. It has 13 positive inputs, 87 live operations and exact specialized
degree 36 at the authenticated compact44 ports. The parent's additional
sign-free calibration, source/provider and endpoint qualifications are
inherited; this review is not a Lean/iPRA theorem, PDF/JSON interpretation,
provider replay or minimum claim.

We independently reconstructed the literal row delta, checked topological
order, uniqueness and liveness, and tested the substitution at 160 signed
integer assignments. The other three residuals do not use u or y, and for
`y=V+u`,

```
u*(y+V)=y²−V².
```

Thus the auxiliary residual is unchanged under the coordinate substitution.

For positivity, at a zero the first and main norms force k>2 by the
consecutive-square exclusion; the reviewed elementary first-Pell descent
gives `k>=8XY²+4`. Consequently `c=eta+Yk>8XY³` and
`Delta=(Y(X+1)+2)²−1<16X²Y²<c³`. The strong norm says
`i²c⁴=Delta*(f²−1)`, so `f²−1>c`. As `f²|(V+c)` and
`0<c−1<=c+1<f²`, no `V∈{−1,0,1}` is possible. Thus `|V|>1`.

The strong norm also gives `Q=(i*c²)²>1`. `Fa=1` then gives
`(Q−1)(y²−V²)=V²−1>0`, hence `|y|>|V|`. If the old u is positive,
`y=V+u>V` forces y positive. Conversely, positive y implies
`u=y−V>0`. Thus both witness maps work without assuming either a sign for V
or a pre-existing old zero in the reverse direction.

The changed auxiliary residual has degree at most 18: `deg(Delta)<=4`,
`deg(Q)<=6`, and `deg(V)<=6`. The unchanged first, main and strong
residuals have degrees at most 14, 13 and 10, so the sum of squares has
degree at most 36. Independently, using input weights `1,2,...,13` and the
authenticated P72/P115 port integers modulo 1000000009, the complete graph
has degree 36 with nonzero leader **168665932**. This proves the lower bound
at those fixed integers.

The independent checker pins the frozen author graph/README, reconstructs the
source delta, authenticates both port bindings and runs the distinct weighted
ray. The author checker was rerun and matched its saved receipt. The finite
controls do not replace the unbounded norm and positivity argument above.

```
python3 -I -S -B reviews/ordinary13-cfold-aux87-independent/check.py > /tmp/cfold-aux87-independent.json
cmp /tmp/cfold-aux87-independent.json reviews/ordinary13-cfold-aux87-independent/result.json
```
