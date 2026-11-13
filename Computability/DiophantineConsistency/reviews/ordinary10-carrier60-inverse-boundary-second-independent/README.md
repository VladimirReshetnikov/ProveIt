# Independent review: 60-operation carrier inverse boundary

The reviewed `research/ordinary10-carrier60-inverse-boundary/` gives an exact 61-to-60 row rewrite and a valid full 60-graph zero at specified positive, **noncompact** ports for which the direct inverse alpha is zero. It is a counterexample to that direct natural-coordinate inverse, not a proof of different existential zero sets, a fixed compact counterexample, or an iPRA theorem.

The old graph has `q=1+b`, `qF=q−F`, `C=qF−alpha`, and `G=alpha+qF*b`. Therefore `G=q*qF−C`. Deleting the old shifted-alpha, C and product rows and adding shifted-C and the two replacement G rows saves exactly one operation. An old zero can be sent forward by `n_C=C−1` provided the separately established old-zero fact C>0. In the other direction, reconstructing the old natural input requires `alpha=qF−C≥1`; under that guard `n_alpha=alpha−1` makes every remaining row and the output identical. The independent checker compares the complete row transformations and tests both guarded maps on bounded inputs.

For the counterexample, independently computed binary Pell powering with first index 45 and main index 67 gives the stated positive tau, k, g and c at `q=2`, `X=34`, `Y=16`, `M=8704`, `A=562`, and `H=2243`. The exact checks verify `0≤eta=c−Yk<k` and `(g−X−a*c)/H` is a positive integer. Setting `R=k−1+U*(g−X−a*c)/H` and `MC=R−3` yields natural ports `(beta,K0,MC,MF)=(1,1,R−3,0)`. Direct independent evaluation of every 60-graph row gives all three residuals and output zero, with `qF−C=0`.

Algebraically setting the old input `n_alpha=−1` makes the old 61-row output zero as well; this confirms the equation identity and precisely locates the obstruction in the **natural input domain**. It does not say that the old graph lacks a different natural zero at those ports. The fixed compact MC is unrelated to the constructed MC and is not covered by this example.

The checker pins both graph sources and the author's receipt, reproduces the latter, independently computes the Pell pairs by binary powering, tests the two guarded coordinate maps and evaluates the literal full graph. No Lean, build, staging, provider/axiom audit, unrestricted inverse or parent/Con(ZFC) claim was made.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary10-carrier60-inverse-boundary-second-independent/check.py | cmp - reviews/ordinary10-carrier60-inverse-boundary-second-independent/receipt.json
```
