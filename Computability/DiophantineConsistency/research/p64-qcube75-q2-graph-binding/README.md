# Binding the symbolic q² zero to the 76Y graph

This independent finite check binds the [symbolic full-zero construction](../p64-qcube75-q2-symbolic-full-zero/README.md) and its [independent review](../../reviews/p64-qcube75-q2-symbolic-full-zero-independent/README.md) to a precisely specified graph modification. It does not execute the enormous witness or independently establish the construction's universal arithmetic argument.

The verifier:

- authenticates `p64-qcube76-independent-y-candidate/graph.json` by SHA-256 and checks its 76 unique rows;
- checks that `q3 := q2*q` is used only in `Y := q3*s`, deletes the first row and changes the second to `Y := q2*s`;
- compares all 75 resulting rows to the separately specified row list in the verifier and checks that each row contributes to the final polynomial;
- expands 21 semantic formulas to explicitly named cut points and compares them to independently written expressions. These cover the q² coordinate, first factor, main carrier and residual, rank, transport, strong norm, auxiliary expression and norm, and final sum of squares;
- authenticates all six frozen author/review packet files by their existing SHA-256 values, without changing them.

The symbolic expression comparison uses only flattening and sorting for associativity and commutativity of addition and multiplication; subtraction stays ordered. It is a structural check, not a general polynomial solver or a Lean theorem. The huge numbers in the symbolic witness are never expanded. The canonical JSON hash of the generated 75-row graph is recorded in `result.json`.

Run from any directory:

```
python3 -I -S -B path/to/p64-qcube75-q2-graph-binding/check.py
```

The deterministic output is frozen in `result.json`, including the graph, author, review and verifier hashes.
