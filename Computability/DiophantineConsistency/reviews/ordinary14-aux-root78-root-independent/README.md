# Independent review: direct positive auxiliary root at 78 gates

**PASS, external standard-integer comparison.** The frozen author packet
`../../research/ordinary14-aux-root78/` has the same positive-zero existence
as the reviewed 79/60 parent for arbitrary integer ports with beta>0. Its
literal graph has 78 live operations and exact degree 60 at the authenticated
compact44 ports. This is not a new Lean/iPRA theorem, PDF/JSON binding,
provider replay or global minimality claim.

The source delta deletes `y=V+u`, `y+V` and their product, adds `V²` and
`y²−V²`, and keeps the other four squared residuals. Over the integers the
old and new auxiliary expressions agree when `y=V+u`, because
`u*(y+V)=y²−V²`. We independently reconstructed the complete row delta,
verified topology and liveness, and tested that equality and all residuals
at 160 signed valuations.

The positive-coordinate maps require an unbounded argument. The first and
main norms give `k>2` by the reviewed consecutive-square exclusion and then
`k>=8XY²+4` by the reviewed elementary Pell descent. Consequently
`c>8XY³` and `Delta<16X²Y²<c³`. The strong equation gives
`Delta*(f²−1)=i²c⁴>=c⁴>c*Delta`, so `f²>c+1`. Since `f²|(V+c)`, none of
`V=−1,0,1` is possible: `c−1,c,c+1` are positive and below f². Thus
`|V|>1`, while the strong norm also gives `Q=(ic²)²>1`.

At an auxiliary zero, `(Q−1)*(y²−V²)=V²−1>0`, so `|y|>|V|`. For an
old positive zero, `y=V+u>V`; a nonpositive y would contradict that strict
absolute-value inequality, so y is a positive new input. For a positive new
zero, `u=y−V>0`, giving the old positive input. Both maps preserve the other
coordinates and all residuals; no sign of V, canonical-witness choice or
calibration theorem is assumed.

The changed auxiliary residual has degree at most 30; the unchanged main
residual also has degree at most 30 by its reviewed cancellation. The first,
strong and guard degrees are at most 22, 22 and 3, so the output degree is
at most 60. Independently, with input weights `1,2,...,14` and authenticated
P72/P115 port integers modulo 1000000009, the complete graph has degree 60
and nonzero leader 482481457. This proves the specialized degree lower
bound.

The checker pins the frozen source, reauthenticates both port bindings,
performs a distinct weighted ray and finite bound/identity controls, and the
author's checker was rerun against its receipt. The finite checks do not
replace the unbounded proof above.

```
python3 -I -S -B reviews/ordinary14-aux-root78-root-independent/check.py > /tmp/aux78-root-review.json
cmp /tmp/aux78-root-review.json reviews/ordinary14-aux-root78-root-independent/result.json
```
