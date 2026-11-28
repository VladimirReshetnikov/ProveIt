# Lean integration plan

Target: ProveIt commit `89d12dd40424f1217fd818d84877b3da52396a3b`, subtree `Analysis/GeneralizedRiemannHypothesis/Lean/grh`. The report's proofs are mathematical derivations from the identified existing lemmas, not elaborated Lean code. The signatures below are specifications/pseudocode. Names of new lemmas are suggestions.

## Stage I: separate the local costs, keep the existing global scalar

1. In `New/UpperBound/Divisibility/LocalDivisibility.lean`, generalize `IsMarked.isOntoUpToColength_prod_scaledHeckeOperator_pow` (line 331) to export the existing bound before the last application of `mul_sum_heckeScalingExponent_le_loss`:

   `m * (∑ ℓ ∈ Λ, (12 * A_ℓ / (m*p) + j_p / (m^2*f)))`

   The proof already has this bound. Preserve the old theorem as a wrapper. Derive the additional bound `14*f*a/p + 1/m`, using the inequalities in the proof of the preceding lemma at line 294. Both bounds must refer to the same image/submodule and colength exponent; taking a minimum of bounds for unrelated witnesses would be invalid.
2. Define a new nonnegative `colengthLoss p` as in equation (3) of the report, using the same branch predicates as `exists_colengthDvd_gaugeLe_compositeLift` (line 407). In the split/large and nonexceptional branches use the existing zero exponent; at N use the existing `m*f*b` bound, before doubling. Reuse the same module and gauge theorem in all four cases. Restrict to integral ramified source forms as in line 494.
3. State the two-budget result schematically:

   ```text
   ∀ p [Fact p.Prime] (ι : embedding at p),
     ∃ S j, ColengthDvd integralRamified S (p^j)
          ∧ j ≤ finrank SourceForm * colengthLoss p
          ∧ (∀ allowed twist and datum and φ ∈ S,
                 composite gauge ≤ p^(allowedLoss p - gain p))
   ```

   All casts and scalar-ring/module types should follow the original theorem. Do not replace its universal chain-datum quantifiers with a fixed twist. Prove `colengthLoss p ≤ allowedLoss p / 2` and `sum colengthLoss[p]*log p ≤ 150*f*a*logB`. The latter follows by bounding the nonsplit exceptional terms by the harmonic sum over all integers below x₁, and the N term by `m*f*b*log N`; use `logX₁_pow_le_logB`, `m_mem`, and `log_N_mem_Icc`.
4. In `ShortAndEnough.lean`, replace the per-translate index bound by `h * K` where `K = 150*f*a*logB` and `h = finrank SourceForm`. Keep the old scalar `invGainFactor` and all existing normalization lemmas for this stage. `ColengthDvd.comap` and the existing grouping by translates remain applicable. Use `(1-b⁻⁸)h ≤ h_r` only in the final assembly (not a new spanning theorem).
5. In `MainInequality.lean`, use the pre-absorption short and long bounds and the improved index allowance. The exact comparison is the report's new main inequality plus `2*b`. This alone proves the asymptotic improvement. If retaining the exact old theorem for *all* data, branch on the large-scale condition or retain the old proof as a fallback; an eventual threshold suffices for the final analytic endpoint.

## Stage II: remove global gain normalization from the maps

### Signed product formula (`New/Reduction/Lattices/Heights.lean`)

Generalize the **proof**, not the definition, of `HeightLe.nonneg_of_one`. Suggested interface:

```text
signed_product_formula
  (A : ℂ) (hne : A ≠ 0) (C Cstar : ℝ)
  (q r : primes → ℝ) (hq : ∀ p, 0 ≤ q p) (hr : ∀ p, 0 ≤ r p)
  (R : Finset primes) (hrs : ∀ p ∉ R, r p = 0)
  (ha : ∀ σ : ℂ ≃+* ℂ, norm (σ A) ≤ exp C)
  (hp : ∀ ι, padicNorm ι A ≤ p^(q p-r p))
  (hbudget : ∀ U : Finset primes, C + ∑ p∈U, q p*log p ≤ Cstar) :
  0 ≤ Cstar - ∑ p∈R, r p*log p
```

`primes`, `embedding`, `padicNorm` above are schematic names, not library types. Reuse the algebraicity lemma in `nonneg_of_one`, the norm/conjugate bound, and `log_product_formula`. Enlarge the finite prime set beyond the numerator and denominator support to include R; justify any extra terms by prime valuations of units. Signed real exponents occur only in inequalities for fixed nonzero algebraic numbers. Do not try to apply a product formula to the varying twist family. The common multiplier from `HeightLe` is retained and used to form the fixed number A.

### Local Gram bound (`New/Reduction/Lattices/TwistedLattice.lean`)

Use the existing `norm_det_mul_det_gram_le_one`, not a new axiom about inner products. For each rational `t > e_p - g_p`, scale the short columns by the positive algebraic number `p^t`. Prove its p-adic norm is `p^(-t)` via integer powers (the approach of `HeightLe.rpow_mul` can be adapted). The same identity holds under the conjugate embedding. Extend clearing matrices by the auxiliary scalar `γ(ξ)` on the auxiliary block. The resulting inequality is

```text
|ι((|γ(ξ)|²)^n' * Dξ)|_p ≤ p^(δ_p + δ'_p + 2*n*t).
```

Pass to the bound with `t=e_p-g_p` using rational density and continuity. The clearing matrices may depend on t. Empty blocks use determinant one. Both embeddings must use the SAME ξ, although the clearing matrices may differ. A separate chosen twist at the conjugate embedding is insufficient.

### Signed comparison

Preserve the proof of the full-basis ratio `D1 = Dξ * Z(1)/Z(ξ)`. Multiply the two original family height bounds to obtain the common multiplier M0 for `(|γ|²)^(-n') * Z(1)/Z(ξ)`. Apply the signed product formula to `A=M0*D1` and use the local Gram bound to supply

```text
q_p = h_p + 2*δ_p + 2*n*e_p,   r_p = 2*n*g_p.
```

Use `CovolumeLe.sumElim` for the infinity bound. The theorem conclusion is `0 ≤ C_y + 2*δ + 2*n*(E-G) + n'*(B_s+B_d) + B_v`. This can coexist with the original `covolume_add_index_nonneg` (zero gains and losses recover its comparison).

### Raw source map and final assembly

* `ShortAndEnough.lean`: export the raw short spanning result directly from the intermediate β and htarget bounds inside `span_short_integralRamified_eq_top`; use `projectedPoincare`, leaving the seesaw constant and group projector in place. Transfer the source local gauge to output integrality for `p^t` by `goodProjTranslate_mem_integralForms`. This scalar belongs on the output; it need not preserve the integral source module. Group vectors by translates to obtain the local signed clearing certificate. Raw and normalized translate images have the same range since the scalar is nonzero.
* `LongForms.lean`: retain the auxiliary forms, twists, ratio heights and full-determinant factorization unchanged. Use the new signed comparison just before the old completion-cost estimates. Keep the explicit `B_s`, `B_d`, and `B_v` rather than absorbing them into `3*L`.
* `MainInequality.lean`: use the existing or adaptive centered spanning and completion theorem. Preserve exact coefficients of H and G; use `H ≥ 0`, `n ≤ d_T`. The final inequality is equation (13) in the report. The new raw maps do not depend on `gainExponent`, `invGainFactor`, or `normalizedPoincare`; keep compatibility wrappers until a dependency search confirms removal is safe.
* `OneSidedBound.lean`: use the old main bound for sufficiently large admissible scales, or expose the new bound. No changes to the analytic criterion, auxiliary-prime selection, or public theorem types are required.

## Verification gates

- Run the exact finite checks included in this archive. They do not establish the universal lemmas.
- Check source anchors against the pinned checkout using `verify_sources.py`.
- Follow the repository's toolchain and build instructions for the readable edition; use its `PrintAxioms.lean` and the independent comparator/kernel-export workflow. Recheck the public theorem types in `src/Statements.lean` and proofs in `src/Main.lean`; verify no new axioms, `sorry`, or trust-base changes.
- Rebuild after removing any now-unreferenced normalization helpers. Record a dependency and proof-size comparison rather than predicting a number of lines saved.

None of these Lean compilation or external verification gates was executed in this session. No `.lean` patch is included because its actual elaboration has not been tested.
