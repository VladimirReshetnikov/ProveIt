# Source-only same-provider direct-K / partial-band join plan

This is a candidate rebuild frontier and proof plan, not a Lean build or an established equality. Start with fresh corresponding sides of the independently audited direct symbolic-K provider. The coefficient-decomposition provider must **not** be overlaid on it: both sides currently have 90 shared `.olean` paths, and the following four hashes differ (the same comparison holds on author and peer):

| Object | direct-K SHA-256 | coefficient-decomposition SHA-256 |
| --- | --- | --- |
| `ArithmeticBinaryCarry` | `05d780a98274a82410933c927c4e01b0a8023d1e80e73cdded6f72a1590e0d08` | `32a0f13a686ad5ab5bda905a3fa8aeaf450d1e5e723eb71c7675020ad5afe682` |
| `ArithmeticBinomLegendre` | `37df80a3c42967ae7c7d06776da4864e824b659b06fad3608a58d8aab361ac92` | `aac6eb68d88ae81aca98299756318be122600445b19189ec91efd136066b68b6` |
| `Compact943Data` | `9ed9ec865af1b8b3794328655ca7cb9161cb8573460c82f80c5db8c35db4bf7b` | `092cf01d0bf249e88f75c78a31eb69f15040dfe985f1e990b19b8d296b9bd9d4` |
| `CompactCoefficientMass` | `4a1745f314085517864a75307f4885f4eaf296ff983a91c0f2eca54f6386db9f` | `e3ac8b31bcc8605ea87030969c7eac84e5369c1be69e73805fcf3b8bfd1dfb4e` |

`scan.json` lists exact source paths, commit bytes, SHA-256 values, imports and requested axiom-report names for this candidate topological order:

1. `ArithmeticCyclicWord` → `ArithmeticWindowCarry`;
2. `CompactSelector` → `CompactSelectorDiv`, plus `CompactCopy` and `CompactSelectorSum` → `CompactSelectorDecoder`; separately `CompactSelectorConverse`; then `CompactDecoderIff`;
3. `CompactTilePayload` → `Compact943Decoder` → `CompactCoefficientDecoder` → `CompactPartialBand` → `CompactPartialBandRotation`.

The direct-K side supplies its own `ArithmeticWindowDigits`, `Compact943Data` and `CompactCoefficientMass`; all newly built objects must resolve on that same side. `ArithmeticCyclicWord` also imports package module `Mathlib.Algebra.BigOperators.Ring.Finset`, recorded separately alongside `Init`. The two workspace arithmetic sources match the retained window-source snapshot bytes at the time of this scan; they are selected sources to rebuild, not permission to reuse the old provider's objects. The uncompiled `TwoBand.lean` and the required K-cast/graph-witness join are not included in these 14 sources and need their own source, dependency and axiom review.

The no-Lean scanner pins the audited direct-K receipt and terminal record, checks each source against exact Git bytes and declared imports in topological order, compares all 150 parent object hashes on each corresponding side, records all four differing overlaps with the coefficient provider, and checks 60 external-project slots, 280 absent target slots and 20 package slots. Normal session 85298 exited 0 with empty stderr; optimized execution was rejected. This does not rerun the parent audit, verify every transitive or dynamic dependency, prove the 14 sources compile against the chosen provider, or freeze a simultaneous snapshot. A real rebuild requires an independently reviewed closure and driver, coherent same-side dependency resolution, all direct/output/source-copy companion guards, exact axiom inventories, sampled resource limits, clean loader, stable HEAD and sole Lean slot. No object from the coefficient provider may be copied into the direct-K overlay merely because its name matches.

## Precise mathematical bridge still to prove

`CompactSymbolicKernelOpaque.paramKernel rho` is a natural term with `rho = 2^67`: two sums indexed by `Fin 943` and `Fin 41`, each with reflected exponents `4393-e` and `5495-e`, plus four bare powers 30,62,1100,2201 and the spatial term `rho^8807*rho^42`. Its model cast should equal `kernelBand position 4393 + kernelBand position 5495 + bareKernel`; `bareKernel` has the five aligned exponents 30,62,1100,2201,8849. The existing `cast_paramKernel` is proved with a **symbolic** radix, but specializing and connecting it to the exact joined sources has not yet been compiled. A promising small lemma for each standard e is `((rho:V)^e) = Exp.exp ((67:V)*(e:V))`: use the standard `cast_exp` theorem, `pow_mul` and cast-of-products symbolically without expanding `2^590069`. Distribute the finite selector and copy sums and use `rho^8807*rho^42 = rho^8849` in the model. The positions and target differences in both definitions are natural subtraction **before** cast; the index bounds `<4393` make their intended reflection interpretation valid, but should be proved separately instead of replacing a natural difference by an unproved model subtraction.

The existing uncompiled `TwoBand.lean` takes that model equality as `hK`, assumes `0<n`, positive modulus and the graph congruence, and proposes to combine two applications of `band_rotation_congr` and the five-monomial congruence. It keeps the temporal `w*C` term separate. Neither its proof nor those hypotheses have been checked in this join. For the same graph-derived N,w one must additionally prove `n=8807*N>0`, `Exp.exp (67*n)-1 = v₀*beta`, the required positive modulus and exact graph congruence. `band_column` also requires `k<n` and `C<Exp.exp (67*n)`.

The temporal factor `w = Exp.exp (R-67*n)` has no proved 67-bit alignment. It must remain a residual or be treated by a separately justified bit-level rotation; it is not an aligned band and is not known to have digit cap 3. The full column, carry/no-carry and clean-target conditions, byte/display binding, machine simulation and internal iPRA equivalence remain separate obligations.
