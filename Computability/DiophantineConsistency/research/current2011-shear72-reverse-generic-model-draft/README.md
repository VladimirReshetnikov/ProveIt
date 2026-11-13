# 72/46 reverse sphere to positive model-natural ordinate

This source-only client composes the distinct unelaborated generic ordered-ring inequality `ShearNonzeroDraft.ordinate_ne_zero` with `Shear72ReverseMagnitudeDraft.positive_magnitude` and `auxiliary_of_same_square`. It assumes `A≥0`, `I≥2`, `y≥1`, and the explicit four-squares-minus-two equation, and concludes a positive model-natural parent ordinate whose square, and hence parent auxiliary factor, match the sheared ordinate. It takes `rest=P²+(QW−1)²` and moves terms of the input equality to the generic theorem's expected order. The generic argument does not need the stronger discrete split on f from the older fact-level draft.

In the actual 72/46 graph, the intended bindings are `A=Delta*(f²−1)`, `I=i*c²`, `P=N0`, `QW=N1*Nt`, `Vr=V` and the displayed child `y`. The exact graph rows and unchanged parent-y dependency are separate verification obligations; this source does not have a literal Lean evaluator or prove that graph zero yields the displayed equality or its bounds. The recorded JSON checker in the magnitude packet only inspects rows externally. Positive inputs and represented current ports are expected to supply those bounds, but the proofs must be supplied and checked; the opposite shear direction and endpoint transfer also remain open.

Both logical imports are prospective names for the pinned `.lean.src` snapshots. Nothing was elaborated; import selection, `ι_le_ι`, ordered-ring tactics, abs representation and axiom reports remain unverified. This is not a graph zero map, a consistency equivalence, or an iPRA derivation. No Lean/build/staging occurred.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/current2011-shear72-reverse-generic-model-draft/check.py | cmp - research/current2011-shear72-reverse-generic-model-draft/receipt.json
```
