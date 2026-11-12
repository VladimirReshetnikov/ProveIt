# Independent review: natural-port 78↔74 source composition

**PASS at source-interface scope.** The pointwise component has direction
`75 zero ↔ 78 zero` at the same natural ports and same positive valuation;
the proposed first leg uses `.mpr` for 78→75 and `.mp` for 75→78. Both
preserve that valuation and the identical positive-beta premise. The second
component has direction `positive 75 zero exists ↔ positive 74 zero exists`
at the same natural port tuple and beta premise; its underlying witness maps
may replace the guard coordinate by h+1 or h−1. Transitivity therefore has
the stated direction and does not claim all 74/78 witnesses coincide.

The checker pins the relevant source files, verifies source signatures and
witness update shapes, runs schematic finite witness-direction controls, and
replays the author receipt. Those controls are not an actual graph-zero search.
All component source drafts, model discreteness, casts, graph/unit facts and
proof tactics remain unelaborated. No coherent provider, checked model/halting
or iPRA endpoint, physical byte/PDF binding, or Lean run is asserted.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary14-78-74-model-composition-independent/check.py | cmp - reviews/ordinary14-78-74-model-composition-independent/observation.json
```
