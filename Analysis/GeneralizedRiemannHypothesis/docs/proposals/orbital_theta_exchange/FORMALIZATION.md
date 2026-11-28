# Lean migration plan

This is an implementation specification, not compiled Lean code. The baseline is `ee10f937fedac0955d28b7b860f4c44fab508204`, readable `Lean/grh`. The mathematical proof is in the companion report. Preserve the existing `Main.lean` theorem statements.

## 1. Add a local orbital module

Suggested file: `src/New/Determinant/Exchange/OrbitalProjection.lean`. Start with the actual `LocProd` type at a finite set of ramified places. Alternatively, use the existing abstract semilocal frame API plus a hypothesis giving normalized bi-invariant Haar measure on each `GL r F` and the local constancy of the character on units. Supply that hypothesis for `LocProd`.

Use existing `IsPrimitiveMatrix`, `HasLeftInv`, `schwartzBruhat`, and `intGL`. The column datum type should be the **submodule** `schwartzBruhat HasLeftInv`, not all functions: Bochner integration of nonintegrable arbitrary functions is not linear. Use the row subtype by transposition. Define `orbitalSection` as a linear map on the Schwartz subtype. Establish integrability pointwise using the continuous left inverse, closed image, and compact support within the full-rank locus. Haar can be obtained by the explicit density `|det|^(-r)` with respect to product additive Haar; verify normalization and both translations. Avoid assuming the character is unitary. In the empty ramified set and zero-rank cases use the trivial-group normalization.

Desired interfaces (pseudocode, not exact Lean syntax):

```
orbitalSection_covariant : J f (y * h) = chi(det h)⁻¹ * J f y
orbitalSection_invariant : J (rho h f) = J f
orbitalSection_ambient   : J (f ∘ (t * ·)) y = J f (t * y)
primitiveProjection     : SB n r →ₗ[ℂ] PrimitiveCovariant n r
primitiveProjection_retract : P (w : SB) = w
primitiveProjection_certificate :
  ∃ finite data (f_i, s_i, k_j, H),
    f = ∑ i, f_i ∧
    P f - f = (index H : ℂ)⁻¹ • ∑ i,j, (rho (k_j*s_i) f_i - f_i)
ker_projection_eq_span : ker(P) = span {rho h f - f}
linear_factor_projection : (∀ h f, Λ (rho h f) = Λ f) → ∀ f, Λ (P f) = Λ f
```

The finite certificate is the essential bridge to the *algebraic* linear map in `EquivariantDifference.lean`. Do not prove factorization by commuting this linear map with an integral. For finite-support partition use compactness of support and clopen sets `U * s`; ordinary one-sided coset representatives suffice. Prove a common principal congruence subgroup fixes the finitely many data, then average over the finite quotient. If the Haar implementation is disproportionately costly, use the same finite certificate and a discrete coset integral, but verify the double-coset index equality needed for bi-invariance.

## 2. Complementary primitive matching

Retain the finite-ring block calculation at `MatchingPartners.lean:57–120` and existing primitive clopen lemmas where useful. Prove the block completion identity: for complementary `x,y`, choose integral left inverse `L` of `y` and right inverse `S` of `x`; the inverse of `[y,S]` is `[L*(1-S*x);x]`. This avoids normalizing the two inverse blocks separately. Prove `det i = det k` by block-unitriangular multiplication.

Define `primitiveMatch : PrimitiveCovariant n b ≃ₗ[ℂ] PrimitiveRowCovariant a n` by evaluating the matching rule at an integral completion of each primitive row, showing completion-independence and local constancy (local section by fixed complementary rows). Prove the analogous inverse. No chosen completion remains in the values of the resulting map.

Define a new relation, initially under a different name, on Schwartz subtypes:

```
orbitalSameSection Φ Ψ := ∀ k,
  J_row Φ (invLastRows e k) = chi(det k) * J_col Ψ (firstCols e k)
orbitalSameSection_iff : orbitalSameSection Φ Ψ ↔ P_row Φ = B (P_col Ψ)
canonicalPartner : SB n b →ₗ[ℂ] SBrow a n := inclusion ∘ B ∘ P_col
canonicalPartner_spec : orbitalSameSection (canonicalPartner Ψ) Ψ
```

Prove translation and inclusion of original `AreMatched` data using Theorem 5.1 and Proposition 5.3 of the report (use names if numbering changes). The local character in `EquivariantDifference.lean:297–298` contains an absolute-value factor, which equals one on integral units; preserve the source proof `h_char` at lines 339–348. The additive character used in Fourier theory is separate and unchanged.

## 3. Construct the equivariant difference directly

At `EquivariantDifference.lean:235–268`, restrict `Λ ∘ₗ D` to the row Schwartz subtype. The existing proof `h_invariant` already gives the precise determinant-twisted translation law. Use the explicit linear factor `Λ ∘ B ∘ P_col` on the column Schwartz subtype. If downstream definitions require maps on the entire function space, extend once by the existing algebraic linear-extension API, not by applying the Bochner integral to arbitrary functions.

At lines 281–349 choose `M = schwartzBruhat HasLeftInv` and `𝒟 = T - c • T'`. For the automorphy and level clauses, use the canonical partner for any `Ψ ∈ M`. For equivariance use the translated partner and the factorization, exactly as the old proof uses `sameSectionPairs.translate_mem`. For original matched pairs use their inclusion theorem; the resulting output statement should remain identical. Keep `thetaLarge_translate_mul`'s scalar formula and `thetaSmall_translate_mul` unchanged (only adapt the relation and membership extraction).

The only other located external use of `mem_sameSectionPairs_iff` is `StableSpacesStandardData.lean:91` (`exists_pow_smul_add_eq`): it needs only the Schwartz property of the matched column function. Prove this directly from the existing clopen/compact primitive locus and local constancy; no orbital construction is needed in that generic semilocal file.

`TheoremForPartners.lean:260` should call the unchanged public theorem as before; do not weaken or reprove its constant-term/vanishing assumptions. Its `exchange_identity` (line 1051) and all downstream norm, determinant, main inequality and zero-exclusion interfaces should remain untouched.

## 4. Acceptance gates

- On the pinned baseline, compile the new local orbital module and all its hypotheses for the actual `LocProd` type. Prove the normalized measure identities, support properties, finite certificate and matching isomorphism without `sorry` or new axioms.
- Compile the new equivariant-difference theorem and `StableSpacesStandardData.lean`, then compile the full readable project. Inspect all references to `commonCosetRep`, `commonCosetSum`, `IsCommonCosetRep`, `localSection`, `sameSectionPairs` before removal. Remove only declarations whose users have been migrated.
- Verify the same theorem statements in `Main.lean` and run `lake env lean scripts/PrintAxioms.lean` with Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. No extra axioms. Run the baseline's independent comparison procedure, e.g. `lake comparator --paranoid` where resources permit; see Andrew Sutherland's verification page for the memory issue of the readable edition.
- Compare source-line counts, dependency closure, elaboration time and checker cost with baseline. The targeted representative/summation block is at lines 136–341, 409–506, and matching bridge at 602–642. Do not treat deletion of that block as a realized net reduction; measure new supporting code too.
- Check interaction with existing proposal implementations by building after each integration. The proposed local interfaces are orthogonal to their mathematical targets, but imports and names may change.

The attached `check_orbital.py` gives exact regression tests. It cannot validate the Lean implementation or the local-field theorem in general. No repository modifications have been made.
