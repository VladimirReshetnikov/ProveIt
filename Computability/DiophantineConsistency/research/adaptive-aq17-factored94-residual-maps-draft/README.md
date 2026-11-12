# AQ17/94 residual-map source draft

This is an **unelaborated** Lean proposal to discharge the two graph-zero
obligations in the [AQ17 model transfer](../adaptive-aq17-factored94-model-draft/).
It contains eight residual comparisons, three vanishing binding identities,
proposed recovery of the three parent coordinates via difference-ring
injectivity, and both model zero maps. The comparisons are stated directly
for AQ17/94 versus AQ20/104 and arbitrary signed ports; no fixed-port beta
assumption is used for this local algebra.

The external checks compare AQ17/94 with AQ17/95, and AQ17/95 with AQ20/104;
they establish the exact finite polynomial identity but do not elaborate the
Lean steps. In particular `parent_bindings`, its cast simplification and all
ring tactics remain proposals. The prior positive-beta requirement in AQ20,
the AQ20 and AQ22 graph maps, the historical provider provenance, and the
111-operation natural graph's connection to positive shifting all remain
separate obligations. A source declaration with no hypothesis is not a
kernel-checked theorem and is not an iPRA endpoint.

Run the bounded, read-only source and graph checks from
`Computability/DiophantineConsistency`:

```
python3 -I -S -B research/adaptive-aq17-factored94-residual-maps-draft/check.py | cmp - research/adaptive-aq17-factored94-residual-maps-draft/receipt.json
```

This does not execute Lean, stage artifacts, validate tactics or authenticate
compiled providers.
