# A 95-gate sign14 ring-rewrite candidate

`build.py` makes two exact integer-ring rewrites of the pinned external
[98-gate candidate](../nine-sharing-sign14-tau-candidate/README.md). Put
`b = beta*(v1+1)` and `q = b+1`. The first identity
`v9*q+b = (v9+1)*q-1` replaces ten repeated copies of the same expanded
subtree. In the `Nt` residual, the second identity is

```
(a*q+q) - (a*c+d+z) - 1 = a*(q-c)+b-d-z,
```

where `a=K0+(v9+1)`, `c=(v2+1)+(v3+1)`, `d=v2+1`, and
`z=(v4+1)*b`. The builder checks both local identities as sparse integer
polynomials, verifies the exact source patterns and four direct assignments,
and constructs a live topologically ordered circuit by exact ordered-subtree
sharing. The result has **95 binary gates**: 38 additions, 17 subtractions
and 40 multiplications, including five squares and their sum. The author run
exited 0; input and generated candidate hashes are in `result.json`.

These are external computations, not a Lean proof for this new JSON. The
formal Lean equivalence to the previously checked sign14 expression, its
degree and iPRA endpoints, fixed-port files and any PDF presentation remain
separate. The gate count is an upper bound under the stated free-leaf sharing
convention, not a minimality claim.

The [independent external audit](../../reviews/nine-sharing-sign14-95gate-candidate-independent/README.md) passed: it separately checks both local polynomial identities, exact rewrites and the live-gate count. It does not establish Lean equivalence.
