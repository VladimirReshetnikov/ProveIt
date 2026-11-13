# A 90-gate sign14 ring-rewrite candidate

`build.py` makes one exact factorization of the pinned
[92-gate candidate](../nine-sharing-sign14-92gate-candidate/README.md). Let
`b=beta*(v1+1)`, `q=b+1`, `d=v2+1`, `g=v3+1` and
`r=b*(b-v2)+g`. It replaces four copies of

```
(b-d)*q^3 + (d+g)*q^2
```

by `r*q^2`. The expression `r` is already used elsewhere in the residuals.
The builder checks the exact source occurrences, normalizes the local
identity as a sparse integer polynomial and checks four direct assignments.
Exact ordered-subtree sharing yields a live **90-gate** binary circuit:
36 additions, 16 subtractions and 38 multiplications, including the five
squares and their sum. The author run exited 0; hashes and counts are in
`result.json`.

This is an external candidate and gate upper bound, not a minimality proof.
Lean equivalence of the new AST, its degree and iPRA endpoint remain unproved.
JSON/PDF and fixed-port file semantics remain separate. The [independent
external audit](../../reviews/nine-sharing-sign14-90gate-candidate-independent/README.md)
passed, checking all four substitutions, the ring identity and live-gate count.
