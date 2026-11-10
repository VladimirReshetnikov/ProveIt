# An 88-gate sign14 ring-rewrite candidate

`build.py` rewrites the pinned [89-gate candidate](../nine-sharing-sign14-89gate-candidate/README.md).
It replaces the unique Nt subexpression `b-(v2+1)` by `(b-v2)-1`, reusing
`b-v2` from another residual. The builder checks the exact source occurrence,
normalizes the local identity as a sparse integer polynomial and checks four
direct assignments.

Exact ordered-subtree sharing gives a live **88-gate** binary circuit:
34 additions, 16 subtractions and 38 multiplications, including five squares
and their sum. The author run exited 0; hashes and counts are in `result.json`.
This is an external candidate and gate upper bound, not a minimality proof.
Lean equivalence, degree and iPRA endpoints for this new AST remain unproved;
JSON/PDF and fixed-port file semantics remain separate. The [independent
external audit](../../reviews/nine-sharing-sign14-88gate-candidate-independent/README.md)
passed, checking the unique rewrite, reused difference and live-gate count.
