# A 94-gate sign14 ring-rewrite candidate

`build.py` rewrites the pinned [95-gate candidate](../nine-sharing-sign14-95gate-candidate/README.md).
Its repeated shared product has the form `t*(t+2)`, where the existing
subexpressions give `t=h-1`. It replaces that product by `h*h-1`, using
`(h-1)*(h+1)=h*h-1`. The builder verifies all five exact source occurrences,
checks the one-variable polynomial identity and four direct assignments,
and constructs a live topological circuit by exact ordered-subtree sharing.
The resulting upper bound is **94 binary gates**: 37 additions, 17
subtractions and 40 multiplications, including five squares and their sum.
The author run exited 0; hashes and counts are in `result.json`.

This is an external ring-rewrite candidate and gate upper bound, not a
minimality proof. Lean has not yet established equivalence of this new AST,
its degree or its iPRA endpoint. JSON/PDF and fixed-port file semantics remain
separate. The [independent external audit](../../reviews/nine-sharing-sign14-94gate-candidate-independent/README.md)
passed, separately verifying the source substitutions, ring identity and live
gate count.
