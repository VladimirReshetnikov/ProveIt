# Pointwise 75↔78 model-zero comparison — source draft

`zero_iff` composes the separately reviewed, unelaborated 75→78 and 78→75
source maps at the **same valuation** and signed integer ports in an arbitrary
IΣ₁ model. Its explicit hypotheses are the beta port cast, beta positivity,
and positivity of all 14 coordinates. The natural-port specialization uses
`P72Root.cast_port` for the beta cast and keeps the same valuation. Neither
statement assumes additional K/mask bounds or a changed witness.

This is a source composition only. The model maps, graph source, imports and
proof tactics have not been elaborated. No provider/Init coherence, machine
halting bridge, checked iPRA endpoint, physical byte/PDF binding, or Lean run
is asserted.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary14-78-75-model-equivalence-draft/check_source.py | cmp - research/ordinary14-78-75-model-equivalence-draft/observation.json
```

The checker validates source interfaces and replays both dependency receipts;
it does not elaborate the Lean statements.

Independent source review: [75/78 pointwise wrapper](../../reviews/ordinary14-78-75-model-equivalence-independent/README.md).
