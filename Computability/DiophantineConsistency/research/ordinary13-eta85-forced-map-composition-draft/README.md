# Eta forcing composed with the 85-to-86 zero-map draft

This is an **unelaborated source-only composition**. It applies the proposed
`EtaNaturalGraphParityDraft.eta_positive` to the exact type of
`EtaUnshift85TransportDraft.ForcedEta K`: for every intended IΣ₁ model and
valuation, an actual 85-prototype zero at `ports K` must have positive eta
coordinate 9. The compact symbolic tuple is the same in both sources and K
is an arbitrary standard natural. The composition adds no premise for
`ForcedEta`, but it does not independently verify the eta proof.

The existing zero-map source increments coordinate 9 when mapping an
86-parent valuation into the 85 child, and uses its predecessor in the other
direction. Its proposed `raise_lower` requires the eta positivity now supplied
by the graph parity source. Under those imported source declarations, the
new `compact_sameNoZero` is stated with the **85 child first** and the exact
**86 parent second**. The coordinate substitution in the two JSON circuits
is checked as an exact row transformation; the large Lean evaluation proof
and the model-natural predecessor argument still require elaboration.

The new `polynomialBridge` and `native_equivalence` retain the explicit
hypothesis

```
PolynomialBridge (EtaShifted86GraphDraft.literal (fun j => (ports K j : ℤ)))
```

for this exact 86-parent and same compact tuple. The proposed native target
is the existing `nativeNoZero(child) ↔ ¬mappedNativeRefutation embedding`;
this source does not establish the parent bridge, reconstruct the earlier
87-parent chain, verify the intended consistency formalization or theory
adapter, or identify K with a concrete kernel or external byte/PDF payload.

All graph factor-unit, graph parity, cast/rank, natural norm, zero-map,
translation, source/provider/axiom and model-building dependencies remain
unelaborated. `#print axioms` appears only as inert source. Neither an
all-model zero equivalence nor an internal-iPRA proof is claimed as checked.
No graph, parent, equation or PDF was changed.

From `Computability/DiophantineConsistency` reproduce the read-only check:

```
python3 -I -S -B research/ordinary13-eta85-forced-map-composition-draft/check.py | cmp - research/ordinary13-eta85-forced-map-composition-draft/receipt.json
```

It pins the source inputs, checks the signatures and exact parent/child row
substitution, and confirms the parent bridge remains in both theorem headers.
It does not check Lean proof terms, provider provenance or physical semantics.
