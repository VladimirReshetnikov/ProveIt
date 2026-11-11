# Independent review: first-residual unscaling to 80 gates

**PASS, external standard-integer comparison.** The frozen author packet
`../../research/ordinary14-unscale-first80/` preserves the complete zero set
at each strictly positive valuation when beta>0. It removes four live gates
and has exact specialized degree 60 at the authenticated compact44 ports.
This review does not establish a Lean/iPRA theorem, literal PDF/JSON binding,
new provider ancestry, unrestricted signed-domain zero equivalence, or
minimality.

We independently reconstructed the complete parent-to-candidate row delta
and checked topology and liveness. Parent M has exactly the two named uses;
Z, M² and M²*D have no additional consumers. For any integer valuation,

```
A0_old=(M*L)²−M²*D=M²*(L²−D)=M²*A0_new.
```

The other four residuals agree. On the stated positive domain,
`M=q³*J*beta>0`; a sum of integer squares vanishes exactly when each
residual does. Hence the two output zeros agree for the **same** valuation.
Their polynomial outputs are generally different; exactly,
`Pold−Pnew=(M⁴−1)*A0_new²`.

The author's bound follows from `L=ell+(k−r)`:
`A0_new=2*ell*(k−r)+(k−r)²−1−ell*k`, of degree at most 12. The retained
main, auxiliary, strong and guard residual bounds are 30, 23, 22 and 3,
so their sum of squares has degree at most 60. Independently, a weighted
ray mapping the 14 inputs to `t,2t,...,14t` and using authenticated P72
and P115 raw ports modulo 1000000009 has exact degree 60 and nonzero leader
345391627. This proves the degree lower bound at those port integers.

The independent checker pins the frozen author graph and README, independently
rebuilds the row delta and verifies topology, sole-use deletion and 160
signed factor/output controls. It reauthenticates both port bindings and
runs the distinct weighted ray. The author's checker was rerun and matched
its saved receipt. Finite controls do not replace the algebraic proof above.

```
python3 -I -S -B reviews/ordinary14-unscale-first80-root-independent/check.py > /tmp/unscale80-root-review.json
cmp /tmp/unscale80-root-review.json reviews/ordinary14-unscale-first80-root-independent/result.json
```
