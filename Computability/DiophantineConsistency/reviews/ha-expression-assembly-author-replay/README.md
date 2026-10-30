# Generic HA equation/source assembler

The two new sources are `HAExpressionAssembly.lean` and `HAExpressionAssemblyChecks.lean`. The author run passed, recording exact source snapshots, full compiler logs, output hashes and the two direct import object hashes. The direct imports are historical objects: their matching sources and all transitive HA/ZFC, Foundation, Mathlib and other dependency closures are not authenticated by this packet. Private independent replay `/tmp/ha-expression-assembly-xjhh42ri` passed with matching source, object and full-log hashes; root replay `/tmp/ha-expression-assembly-vgttkwsl` also passed with the same hashes. Author, private and root snapshots, complete logs and terminal states are recorded.

For an arbitrary finite natural expression, the source-semantic theorem identifies its exact Foundation no-zero sentence with absence of a zero in every IΣ₁ model. Given the explicit all-model no-zero/machine bridge, the assembler constructs an actual IΣ₁ proof and an actual HA proof equivalence between the expression's `ArithmeticExpression.noZeroSentence` and Foundation's ordinary ZFC consistency sentence, using the existing checker/source bridge and negative translation. It does not prove the 87-gate bridge or discharge any assumption about that expression.

```sh
python3 Computability/DiophantineConsistency/reviews/ha-expression-assembly-author-replay/replay.py \
  --parent /tmp/hacurrent-client-audit-20261029/lib \
  --expected Computability/DiophantineConsistency/reviews/ha-expression-assembly-author-replay/author/state.json
```
