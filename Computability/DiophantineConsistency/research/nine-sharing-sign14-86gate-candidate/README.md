# An 86-gate sign14 ring-rewrite candidate

`build.py` rewrites the pinned [87-gate candidate](../nine-sharing-sign14-87gate-candidate/README.md).
It applies `(a+r)-R=a-(R-r)` at four AST occurrences representing two
shared residual subexpressions, introducing a single reusable `R-r` node.
The builder checks the occurrences, normalizes the identity as a sparse
integer polynomial, and compares residuals at four assignments.

Exact ordered-subtree sharing gives a live **86-gate** binary circuit:
30 additions, 18 subtractions and 38 multiplications, including five squares
and their sum. The final author run exited 0; hashes and counts are in
`result.json`. The first attempted run rejected an expected-occurrence count
of two because the AST contains two copies of each squared subexpression;
the final builder checks all four. This is an external candidate and gate
upper bound, not a minimality proof. Lean equivalence, degree and iPRA
endpoints for this AST remain unproved; JSON/PDF and fixed-port file
semantics remain separate.
The [independent external audit](../../reviews/nine-sharing-sign14-86gate-candidate-independent/README.md)
passed, checking the four AST occurrences, the ring identity and the live
gate count against the pinned 87-gate input.
