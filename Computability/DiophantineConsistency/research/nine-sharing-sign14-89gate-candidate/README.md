# An 89-gate sign14 ring-rewrite candidate

`build.py` makes one exact rewrite of the pinned
[90-gate candidate](../nine-sharing-sign14-90gate-candidate/README.md). Put
`b=beta*(v1+1)`, `q=b+1`, `d=v2+1` and `g=v3+1`. It replaces the unique
Nt subexpression `q-(d+g)` by `(b-v2)-g`, reusing `b-v2` from the factored
rank term. The builder checks the exact source occurrence, normalizes the
local identity as a sparse integer polynomial and checks four assignments.

Exact ordered-subtree sharing gives a live **89-gate** binary circuit:
35 additions, 16 subtractions and 38 multiplications, including five squares
and their sum. The author run exited 0; hashes and counts are in `result.json`.
This is an external candidate and gate upper bound, not a minimality proof.
Lean equivalence, degree and iPRA endpoints for the new AST remain unproved;
JSON/PDF and fixed-port file semantics remain separate. The [independent
external audit](../../reviews/nine-sharing-sign14-89gate-candidate-independent/README.md)
passed, checking the unique rewrite, reused difference and live-gate count.
