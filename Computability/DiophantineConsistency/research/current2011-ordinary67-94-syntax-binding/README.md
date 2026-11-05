# Current 67/94 graph-to-syntax comparison

`check.py` parses the complete pinned [`Carrier94Syntax.lean`](../../Lean/DiophantineConsistency/Carrier94Syntax.lean) expression, and independently converts it and the 67-row [`polynomial.json`](../current2011-ordinary67-94-candidate/polynomial.json) to hash-consed expression DAGs. It checks witness order, 19 common cuts, all live rows and leaves, all four actual-port byte hashes, and the complete output. Multiplication and addition are compared modulo associativity and commutativity. The strong factor uses `(1+I²)−Aaux` in Lean and `1+(I²−Aaux)` in the graph, so an additional exact signed-additive normalization is checked for that factor before comparison of the full output. A changed-witness control is rejected.

This is an external source/graph equality check over commutative rings. It does not compile `Carrier94Syntax`, bind a Lean object to this source, or establish the all-model/iPRA endpoint; those require a coherent checked provider. Degree and port-specific data are independently addressed in the candidate packet.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/current2011-ordinary67-94-syntax-binding/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `cfd87109087e1786ff9b506230f5e5f998ad833d627c3a050c514c39dce1891d` |
| `result.json` | `6df0d0b95ebc667a93b744a449d4e8de01685d83ead3f2992e5721b1cfe5151b` |
| `Carrier94Syntax.lean` | `b68f54257ff1ebab090ed45e83d6c3719be51ccb0f7a7f03822e333bbb43ea8d` |
| `polynomial.json` | `d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb` |
