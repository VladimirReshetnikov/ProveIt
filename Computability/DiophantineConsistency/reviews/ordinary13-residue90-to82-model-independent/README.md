# Independent source review: direct 90 to positive-shifted 82 transport

The generated positive-parent literal and residual sources reproduce all 82 parent graph rows, all 13 variable positions, four ordered ports, and residual order `A0,A1,Fam,g72`. The natural 90 graph is exactly the parent at the mixed substitution: indices 0, 3, 6, 11 and 12 (J, f, X, y, gamma) are unchanged and each of the other eight coordinates is increased by one. The four source relation statements and complete output equality have this orientation at arbitrary signed ports.

For a positive-parent zero the draft subtracts one only from those eight shifted coordinates and keeps the five forced values; applying the mixed map recovers the parent valuation. In the opposite direction it needs all five unshifted values positive to form a positive parent valuation, supplied by the separate proposed J, X, f/y and gamma source declarations. Their signed norms, model divisibility, Pell/rank and provider obligations remain unelaborated; K is an arbitrary standard natural. No extra positivity of the original shifted coordinates is required.

The native client explicitly assumes `PolynomialBridge` for the **positive-shifted 82 parent**; the draft does not construct it. Nor does it identify its symbolic K and ports with authenticated compact bytes or any current-2011 PDF. Source structure, model map directions and parent bridge premise were independently checked, and the author receipt reproduces; Lean tactics, imports and axiom reports have not been executed, so this is not an end-to-end iPRA proof.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue90-to82-model-independent/check.py | cmp - reviews/ordinary13-residue90-to82-model-independent/result.json
python3 -I -S -B research/ordinary13-residue90-to82-model-draft/check.py | cmp - research/ordinary13-residue90-to82-model-draft/receipt.json
```
