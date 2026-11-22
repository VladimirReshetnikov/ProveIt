# Lean implementation of finite rational Helly

Run `lean Helly.lean` with Lean 4.19.0. The only import is `Std`. A successful run emits no diagnostics. The examples at the end use kernel reduction with `decide` and include zero-dimensional, rank-deficient, and full-rank rational input.

`ConstructiveHelly.QPoint.hellyExact d n C table` returns a rational point together with a proof that it belongs to every set `C i`, where `i : Fin n`. The table returns a point and its membership proofs for each duplicate-free list of `min n (d+1)` labels. A table keyed by subsets may ignore order. When `n < d+1`, the required subfamily is the whole family. When `n = 0`, the input table can supply the rational origin for the empty subfamily.

| Declaration | Verified result |
| --- | --- |
| `ConvexSet`, `HullTree.eval_mem` | Extensional membership and closure under the rational blends with positive integer weights. Every positive rational pair occurs after common rescaling. |
| `RadonCertificate.avoid` | A set that contains all but at most one input contains the certified intersection of the two disjoint hulls. |
| `solve` | Recursion on the number of labels constructs the intersection witness from a Radon operation. Each recursive call deletes one position. |
| `QPoint.kernelPool_positive`, `kernelPool_equations`, `kernelPool_nonzero` | For `d+2` homogeneous integer columns, a nonzero coefficient vector annihilates each of `d+1` rows. The proof preserves a coordinate private to each surviving coefficient vector. |
| `QPoint.radon_complete` | Splitting coefficients by sign and weighting by point denominators produces nonempty, disjoint hull expressions with equal rational evaluations. The Boolean certificate checker succeeds. |
| `QPoint.hellyExact` | The local table for distinct subsets of the exact Helly size suffices for every finite family. Deduplication and padding are implemented. |

The final Lean declaration has no unresolved arithmetic hypotheses. The following command appends an axiom query to a disposable copy.

```sh
cp Helly.lean HellyAudit.lean
printf '\n#print axioms ConstructiveHelly.QPoint.hellyExact\n' >> HellyAudit.lean
lean HellyAudit.lean
```

Lean 4.19.0 reports `[propext, Quot.sound]`. The source contains no `sorry`, no custom axiom declaration, and no classical-choice dependency for the endpoint. The checked formalization works in Lean's type theory. The report gives the separate quantifier-free induction and coding argument for iPRA.
