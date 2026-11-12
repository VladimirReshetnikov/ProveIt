# Residue-90 symbolic compact tuple: source-only clients

These two inert `.lean.src` files propose only port-tuple equalities. They have **not** been elaborated by Lean, staged or checked against a compatible provider closure. They add no graph no-zero theorem or iPRA endpoint.

`Residue90CompactTuple.lean.src` chooses

```text
chosenKernel = CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho
integerPorts K j = ((Residue90CompactPortBoundsDraft.ports K j : Nat) : Int).
```

The proposed `chosen_integer_ports` equates that tuple to `CompactSymbolicModelIff.p` by unfolding the existing matching source definitions. The retained 13-positive 87-operation endpoint `IPRAOrdinary13.expression` also uses that same `p`; the tuple statement does **not** relate its graph to the 13/90 graph. The arbitrary-K variant requires an explicit equality `K=chosenKernel`. It does not show that an externally supplied K or file has that value.

`Residue90CompactByteTuple.lean.src` separately proposes equality with `CompactBytePortsModelIff.byteP` by composing `chosen_integer_ports` with the inverse of the existing `byteP_eq`. That tuple decodes each closed Lean list using `Nat.ofDigits 256` in **naturals**, then casts to integers. Its fourth component is the once-shifted `betaNat+highNat`; no second beta is added. The source-level byte theorem refers to closed Lean recipes, not the contents of any gzip, JSON, TeX or PDF file.

The predecessor [compact-port provenance audit](../../reviews/ordinary13-residue90-compact-port-provenance-audit/) separately rechecks both P72/P115 payload copies and external decimal-display comparisons. These observations do not discharge a Lean equality for filesystem bytes, physical PDF semantics or a decimal-seed interpretation. The maintained root equation has a different coefficient tuple from this compact one. The 82↔84 and other required graph/parent bridges, iPRA theory and endpoint alignment, `#print axioms` results, and complete source/object/package provider provenance are also not supplied here.

`Residue90CompactPortBounds` is an inert research source and must be made available as a module in any later build; `Residue90CompactTuple` is likewise needed as the local provider for the second source. The byte client imports `CompactBytePortsModelIff` and its transitive model/byte provider chain; the pinned lexical sources and old receipts are not a successful build of these clients. A future build must select compatible providers, preserve evidence and check elaboration and axiom reports. The proposed `rfl`, `subst` and transitivity proofs are untested.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-residue90-compact-tuple-client-draft/check.py | cmp - research/ordinary13-residue90-compact-tuple-client-draft/result.json
```

The deterministic checker pins both drafts and the exact tuple, endpoint and predecessor source signatures. It does not invoke Lean, authenticate compiled providers or formalize external files.
