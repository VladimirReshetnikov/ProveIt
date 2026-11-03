# The trace75 transport quotient is below any strong root

`Trace75KappaRoot.quotient_below_root` is checked in every supported IΣ₁ model
for arbitrary natural ports with positive model beta and ten positive
coordinates. Given a model `kappa` and `f` satisfying the actual graph
equations `K=H·ι(kappa)` and `1+Delta·U²·E=f²`, it proves `kappa<f`. The
theorem does **not** assume the graph value is zero: the quotient and root
equations are explicit hypotheses. It derives `kappa<c<f` by bounding the
actual signed K below H times c and comparing the strong-root square with
`c²`. The result is a prerequisite for a possible carrier-sign normalization;
it does not itself normalize a zero, prove the trace73 center bound, or imply
an equivalence.

The bounded author run `observations/kappa-attempt02/` and its tool session
28864 exited 0; `#print axioms` reports
`[propext, Classical.choice, Quot.sound]`. The resulting object
`/tmp/trace75-kapparoot-ewby3i34/Trace75KappaRoot.olean` has SHA-256
`ba694f90388cf52b3b692d4c590d59298fdc1b626c819246de0e228f3f3e10f1`.
Source, runner and terminal SHA-256 are respectively
`1049e58b90157da78131fec8fbf2d94c4695d08e7b54e4157b4830755501c91c`,
`e527d8c3cce52acfb5588bc5002d6c2f6a046a36387a6b7c341d00b280376cc6`,
and `d12f8f26a232dd2a1e60a87848e18418c0925ccb526e19f52794f343e2c468be`.
Attempt01 failed on an unavailable strict-multiplication instance; its source
and diagnostic are retained, and the accepted version uses non-strict
monotonicity with contradiction. The direct fresh trace75 provider and selected
shared project/package objects are pinned; the complete transitive and
package/dynamic ancestry and independent Lean replay remain outside this run.
