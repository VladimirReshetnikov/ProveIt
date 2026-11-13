# 78 own-zero to 75 same-coordinate zero — source draft

`zero_of_78_zero` proposes a pointwise forward transfer in any model of
IΣ₁, at arbitrary signed integer ports and the **same** natural valuation.
It has no positivity or port-bound hypothesis. The 78 own zero gives its
five residual equalities via the source-only `fiveSquares_eq_zero_iff`; the
separate [ring factor client](../ordinary14-78-75-ring-client-draft/) sends
these equalities to five 75 factors equal to one, so the 75 product vanishes.
All model/graph/ring imports and tactics remain unelaborated.

No 75→78 implication is proved here. That reverse direction must obtain the
four negative-unit exclusions and a lower bound on the first parameter from
the **75 own zero** and appropriate positive-domain assumptions. Provider
closure, object/Init compatibility, arbitrary-model endpoint, iPRA, and
physical byte/PDF binding remain open. No Lean run was performed.

Run the source-interface checks, finite residual controls, and ring-client
receipt replay from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-78-to-75-model-map-draft/check_source.py | cmp - research/ordinary14-78-to-75-model-map-draft/observation.json
```

These checks do not elaborate the Lean source or prove the model statement.

Independent source review: [78 to 75 model map](../../reviews/ordinary14-78-to-75-model-map-independent/README.md).
