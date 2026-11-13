# Independent review of the bounded auxiliary-leading obstruction

The four claimed homogeneous leaders and the stated k-divisibility obstruction are mathematically consistent with the pinned graph. No concrete discrepancy was found. The author's exact symbolic checker and receipt reproduce. Independently, this review evaluates the whole 72-row graph on many symbolic rays, checks the four predicted top coefficients and degree ceilings, and tests a specialization that exposes why the correction cannot cancel the leading auxiliary term. Those finite ray checks do not replace the author's symbolic polynomial computation.

For `k=eta+zeta`, set `i=gamma=0`, all other relevant leading variables and beta to 1, and write `eta=k`, `zeta=0` at the homogeneous level. Then the degree-23 part of U is `−2k`, the degree-22 part of P is `−k²`, and the leading H and QW parts vanish. A putative degree-at-most-one multiplier on P cannot produce the k-linear term needed to cancel U. Equivalently, before this specialization U's leader is divisible by k but not by k², while P's leader is divisible by k². This is an exact polynomial argument over the fixed-port rational coefficient ring when beta is nonzero; the specialization is not an allowed positive witness and proves no solution or zero-map claim. The multiplier degree limits are indispensable; cancellation among higher-degree products is outside scope.

The author's degree-ceiling propagation is sound at the level of its stated invariant: addition takes the maximum lost ceiling, while multiplication bounds a discarded contribution by the discarded ceiling of either input plus the other's retained top degree. A discarded-by-discarded product is covered because each discarded ceiling is strictly below that input's retained top. It aborts when cancellation leaves a retained top at or below a discarded ceiling, or support exceeds its guard. This is source inspection of the checker, not a machine-checked proof of the implementation or an iPRA result.

The absence of higher-degree cancellation, full graph equality, Lean evaluator and degree proof, witness maps, and iPRA endpoint remain separate. No global minimality claim follows. The checker pins both packets, reproduces the author's result and performs independent univariate-ray diagnostics; from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/current2011-shear-aux-leading-obstruction-independent/check.py | cmp - reviews/current2011-shear-aux-leading-obstruction-independent/receipt.json
```

No Lean/build/staging or author-source edits were performed.
