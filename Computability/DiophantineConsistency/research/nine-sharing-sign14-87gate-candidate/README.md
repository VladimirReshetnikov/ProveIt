# An 87-gate sign14 ring-rewrite candidate

`build.py` rewrites the pinned [88-gate candidate](../nine-sharing-sign14-88gate-candidate/README.md).
In its unique Nt expression it uses the integer-ring identity
`x+((b-i)-1)-(z+1)*b=(x-i)-1-z*b`. The builder checks the exact source
occurrence, normalizes the identity as a sparse integer polynomial, and
compares the residuals at four assignments.

Exact ordered-subtree sharing gives a live **87-gate** binary circuit:
32 additions, 17 subtractions and 38 multiplications, including five squares
and their sum. The author run exited 0; hashes and counts are in `result.json`.
This is an external candidate and gate upper bound, not a minimality proof.
Lean equivalence, degree and iPRA endpoints for this AST remain unproved;
JSON/PDF and fixed-port file semantics remain separate.
The [independent external audit](../../reviews/nine-sharing-sign14-87gate-candidate-independent/README.md)
passed, checking the rewrite and the live-gate count against the 88-gate input.
