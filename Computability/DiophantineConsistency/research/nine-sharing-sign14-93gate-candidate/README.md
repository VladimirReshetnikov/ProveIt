# A 93-gate sign14 ring-rewrite candidate

`build.py` makes one ring rewrite of the pinned
[94-gate candidate](../nine-sharing-sign14-94gate-candidate/README.md). With
`b=beta*(v1+1)`, `i=v2` and `g=v3+1`, it replaces the repeated term

```
b*(b+1)+g-b*(i+1)
```

by `b*(b-i)+g`. The builder checks all four exact source occurrences, an
independent sparse integer-polynomial normalization of the local identity,
and four direct assignments. Exact ordered-subtree sharing then yields a
live circuit of **93 binary gates**: 37 additions, 17 subtractions and 39
multiplications, including the five squares and their sum. The author run
exited 0; input/output hashes and counts are in `result.json`.

This is an external candidate and gate upper bound, not a minimality proof.
Lean equivalence of this new AST, its degree and iPRA endpoint are not yet
proved. JSON/PDF and fixed-port file semantics remain separate. The
[independent external audit](../../reviews/nine-sharing-sign14-93gate-candidate-independent/README.md)
passed, separately verifying all four substitutions, the ring identity and
the live-gate count.
