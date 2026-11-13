# A 92-gate sign14 ring-rewrite candidate

`build.py` makes one exact reassociation in the Nt residual of the pinned
[93-gate candidate](../nine-sharing-sign14-93gate-candidate/README.md).
Writing its existing subexpressions as `x`, `b`, `d`, and `z`, it replaces
`((x+b)-d)-z` by `(x+(b-d))-z`. The difference `b-d` is already used in
another residual, so exact ordered-subtree sharing removes one subtraction.

The builder verifies the unique exact source occurrence, the integer-ring
identity and four direct assignments. Its live topological circuit has
**92 binary gates**: 37 additions, 16 subtractions and 39 multiplications,
including five squares and their sum. The author run exited 0; hashes and
counts are in `result.json`.

This is an external candidate and gate upper bound, not a minimality proof.
Lean equivalence of the new AST, its degree and iPRA endpoint are not yet
proved. JSON/PDF and fixed-port file semantics remain separate. The
[independent external audit](../../reviews/nine-sharing-sign14-92gate-candidate-independent/README.md)
passed, checking the unique reassociation, the reused difference and the live
gate count.
