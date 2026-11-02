# Same-witness graph-to-two-band bridge: source-only plan

This is a proposed interface and proof route, not a compiled theorem. The goal is to apply the two-band modular congruence to the same graph witness and the same N and w provided by `CompactSameWitnessSaturation.fixed_graph_saturation`. Its source is `../compact44-same-witness-saturation-prototype/CompactSameWitnessSaturation2.lean`. The relevant two-band theorem is `TwoBand.combined_congr` in `../compact44-two-band-rotation-prototype/TwoBand.lean`; `CompactPartialBandRotation.band_column` is in `../compact44-partial-band-rotation-prototype/CompactPartialBandRotation.lean`.

Quantify over a model `V` with the existing `ORingStructure V` and `V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁` instances, `K : ℕ`, `pos : Fin 41 → ℕ`, and `v : Fin 12 → V`. Assume `hv : ∀ j, 0 < v j` and `hz : InternalZero (literal (fun j => (ports betaNat K lowNat highNat j : ℤ))) v`, using the exact fixed beta and ports of `fixed_graph_saturation`. Set

```
p := ports betaNat K lowNat highNat
q := 1 + v 0 * (p 0 : V)
R := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
C := q-v 1-v 2
```

The existing theorem returns a single pair `N w : V` together with positivity, alignment, its graph congruence, digit bounds and two `NoCarry` statements. Keep this pair intact in the bridge conclusion. Define `n := 8807*N`, `M := Exp.exp (67*n)-1`, and `F := v 1`. The specific additional premise for applying the current two-band theorem is the model equality

```
(K : V) = kernelBand pos 4393 + kernelBand pos 5495 + bareKernel
```

This is a real assumption until a separately checked cast and finite-data binding discharges it. Because `ports betaNat K lowNat highNat 1 = K`, the source theorem's graph congruence has the required coefficient. The port index reduction should be checked explicitly in the coherent provider.

The proposed local derivation is:

1. From `0<N`, obtain `0<n`. Use associativity/commutativity of multiplication to rewrite the already supplied `q = Exp.exp ((67*8807)*N)` as `q = Exp.exp (67*n)` without expanding model exponents.
2. By the definition of `q`, obtain `M = v 0 * (p 0:V)` and hence `0<M` from the same witness's positive modulus. Rewrite its graph congruence as `(((K:V)+w)*C)%M = F`.
3. Apply `TwoBand.combined_congr` using the explicit model K equality. Preserve the conclusion's `w*C` residual as a separate summand.
4. For `band_column`, derive `C < Exp.exp (67*n)` by `C ≤ q-v 1 < q`: positivity of q follows from the alignment and positivity of `v 1` is an input. Supply a model index `k<n` separately. Rewrite the existing same-witness digit bound to `∀ k<n, dig 67 C k≤3` using `n=8807*N`.
5. State the existing two `NoCarry` facts with that same `N,w` and original graph ports. They do not themselves prove no carry for the entire finite family or establish a clean target column.

All arithmetic identities and rewriting steps above require a Lean check; this plan makes no compilation claim. Existing coefficient-decomposition and direct-K providers have four divergent objects, so no combination of their old objects is justified. The author-only coherent rebuild in `../compact44-direct-k-band-join-exploration/OBSERVATION.md` offers an exploratory same-side base; a paired claim requires a separately reviewed coherent build. The cast bridge, finite external-data binding and equality to the retained coefficient bytes or displayed expression remain separate. In particular, `w=Exp.exp (R-(67*8807)*N)` need not be a whole radix-67 rotation, and no bound on digits of `w*C` is supplied by the digit bound for C. This proposed metatheoretic statement also does not establish definability or iPRA provability.
