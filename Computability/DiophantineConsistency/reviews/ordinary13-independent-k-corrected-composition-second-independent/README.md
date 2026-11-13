# Independent source review: rank orientation alternative and selected composition

The isolated `ordinary13-independent-k-rank-orientation-repair` source differs from its original only by replacing the one final `linear_combination h` with `linear_combination -h`, plus the distinct namespace and axiom-query names. The original helper states `ι(rank)=signed`, while the target is `signed=ι(rank)`. Negating the equality supplies the direction expected by the installed `linear_combination` side condition; this is a source-level correction candidate, not observed Lean elaboration.

The selected `ordinary13-independent-k-positive-corrected-composition-draft` differs from the original composition only in the imported rank module, its rank namespace references, and its own distinct namespace and axiom-query names. The module basename matches the corrected source filename; the corrected source declares each referenced `rankExpr`, `first_norm_F_lt_q` and `rank_representation`. The original graph-fact module and its zero-k contradiction call remain selected. The exact fixed-child zero, valuation and natural rank argument are unchanged.

The independent checker pins both original and alternative sources, reproduces both authors' receipts, verifies exact source transformations and independent diff hunks, and checks the referenced declaration and module names. The check is lexical: it does not authenticate providers, elaborate the sign change or either composition, validate model casts/tactics, inspect transitive axioms or prove an iPRA endpoint. No eta≤k or parent-child zero-map claim follows.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-corrected-composition-second-independent/check.py | cmp - reviews/ordinary13-independent-k-corrected-composition-second-independent/receipt.json
```

No Lean, build or staging was performed.
