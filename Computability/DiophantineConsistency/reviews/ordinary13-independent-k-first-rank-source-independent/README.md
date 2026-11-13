# Independent source review: first norm and rank window

The mathematical coefficient and rank bounds in [the draft](../../research/ordinary13-independent-k-first-rank-model-draft/README.md) are sound under their stated model-natural and difference-ring hypotheses. The draft nevertheless has a concrete elaboration hazard in its `C>0` branch: `linarith` is asked to infer the discrete unit gap `A≤Q−F'−1` directly from `0<C`, where `C=Q−F'−A`. Linear arithmetic over an ordered ring supplies only `A<Q−F'`. The fact that Q, F' and A are embeddings of model naturals is essential and is not expressed by that inequality alone.

A rational assignment satisfying all the displayed arithmetic hypotheses including the first norm, but violating that unit gap, is `Q=4`, `B=3`, `F'=1`, `A=5/2`, `D=1`, `r=5/6`: then `C=1/2`, `P=−1/2`, and `(B*r−P)²=B²`, yet `A>Q−F'−1`. This is **not** a counterexample in the intended model-natural interpretation; it demonstrates why ordered-ring linear arithmetic cannot recover the needed discreteness without an explicit bridge. A source repair can reflect `(F+alpha)<q` via `ι_lt_ι.mp`, apply the model-natural successor inequality, and cast it back, or supply an equivalent discrete-order lemma. The reviewed original is unchanged. No Lean execution was used to observe an actual tactic error.

For the nonpositive-C branch, `P=C*D−F'<0`; the signed square identity and positivity give `B*r−P=B`, so discrete natural r is zero and `P=−B`. With `t=−C≥0`, it follows that `F'=B−tD`, `A=1+t(D+1)`, and `G=Q+t+Q*tD`. The natural lower bounds `D≥1` and `F'≥1` give `t≤tD≤Q−2`, yielding `G≤Q²−2`. This verifies the signs and arithmetic in the branch, with casts and the use of `mul_self_eq_mul_self_iff` still subject to elaboration.

For the rank theorem, beta,J>0 give `Q=beta*J+1≥2`, and natural strict mask bounds give `L≤beta−1`, `M≤2beta−1`. Multiplication by nonnegative factors bounds the signed coefficient and mask terms, and the resulting expression is strictly below Q⁴. The source's argument order at the final call matches the separately pinned `zero_k_impossible` helper: q, X, Y, s, R, eta, gamma, z, followed by q positivity, s positivity, Y's factorization, the rank bound, main shape and norm. It does not bind the graph or extract any norm from the output.

The receipt reproduces the author's checker, checks the precise helper call, verifies the rational counterexample to the implicit discrete step, and exercises finite natural examples for both coefficient branches and the rank bound. These controls are not a proof of arbitrary-model validity or Lean elaboration. Cast instances, nonlinear tactics, imports, provider selection and all transitive dependencies remain unverified. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-independent-k-first-rank-source-independent/check.py | cmp - reviews/ordinary13-independent-k-first-rank-source-independent/receipt.json
```
