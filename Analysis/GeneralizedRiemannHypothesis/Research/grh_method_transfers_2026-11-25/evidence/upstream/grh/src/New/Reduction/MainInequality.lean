import New.Determinant.Twist.LongForms
import New.Reduction.ShortAndEnough

/-!
# The main inequality

One covolume, corrected by an index, is bounded from both sides. Write `dim` for the dimension of
the target (`targetDim`), `mainAmount` for the main amount and `rem` for the total remainder
(`totalRemainder`), weighted sums over primes less their expected values. Theorems A and B give a
family of `n ≤ dim` target forms, a bound `V` for the logarithm of the squared covolume of its lifts
(`TwistedLattice.CovolumeLe`) and a bound `δ` for its index (`TwistedLattice.IndexLe`). Up to
errors,

    mainAmount ≤ (V + 2 δ) / dim ≤ mainAmount - (n / dim) m rem,

where the lower bound is Theorem C. The main amount cancels.

Notions from other files:

* `Data P`: the data for the parameters `P` (a modulus `q₀` and a prime `d`). They bundle
  scales `x`, `x₁`, `b` in prescribed ranges (`D.logB = log b`), the number `D.m` of lifts, a set
  of places of the CM field `D.E`, the `b`-places, which carry the weight `b`, and primes for the
  levels. `D.a = x b`, and `D.f` is the number of infinite places of `D.E`.
* `D.normalizedPoincare g`: the translate `g 𝔭` by `g : D.chosenGL` of a fixed linear map `𝔭` from
  the source `D.ramifiedSourceForms` to the target `D.targetForms`.
* `D.integralRamified`: the source forms that are integral at every `ι : PrimePadicIso`.
* `D.errorUnit`: the unit of loss `f a log³ b`.

## The inputs

* Theorem A: (a) `span_short_integralRamified_eq_top` (size) and (b) `indexLe_normalizedPoincare`
  (index).
* Theorem B: `enough_forms`.
* Theorem C: `integral_forms_long`, from a twist for each prime
  (`TwistedLattice.covolume_add_index_nonneg`) and the height of `Z(1) / Z(ξ_ι)`
  (`heightLe_chainDeterminant_one_div`).
* Hadamard's bound for the covolume: `TwistedLattice.covolumeLe_of_normSqAt_le`.
* The sign of the main amount: `mainAmount_nonneg`.

## What cancels, and where

* The main amount, between the upper and the lower bound: the comparison step of
  `star_inequality`.
* The gains `∑ gain_l log l` in the size of the chain, against `log c_B`:
  `span_short_integralRamified_eq_top`.
* The constant `c₁ = (logDerivMean d 1 1).re`, between the period and the expected value
  `a (log (a / κ̄) + c₁)` of the prime sums:
  `jetSize_sub_mainPrimeSum_le`.
* The excesses `a log (κ̄ M rd_E / 2π)` of the `m` lifts, against `a log N`, up to `O(a log b)`.
  Here `κ̄` is the geometric mean of the weights `κ` over the `f` places and `rd_E` is the root
  discriminant of `E`:
  `mul_jetSize_sub_mainPrimeSum_sub_le`.
* The main terms `log x`, `log x₁` and `c₁` of the prime sums, against their expected value:
  `totalRemainder_eq`.
* A constant that depends on `q₀`, between the two cut-offs: `sum_aPlaces_primeSum`.

## The errors per dimension

| source   | where             | amount                              |
|----------|-------------------|-------------------------------------|
| size     | Theorem A (a)     | `f a log⁴ b`                        |
| index    | Theorems A (b), B | `20 log (1 + 2 b²) · f a log³ b`    |
| covolume | Theorem C         | `3 f a log⁴ b`                      |

The index enters twice, and the table shows the doubled amount. The family has `n ≥ dim / 2`
members, so `m rem` is at most twice the sum, and twice the sum is at most `f a log⁵ b`. The scales
are listed in `New.Reduction.Data.Sizes`.

## Relation to the literature

Earlier bounds for sums over primes by size against divisibility: Pritsker, The Gelfond–Schnirelman
method in prime number theory, 2005; Granville–Stark, ABC implies no Siegel zeros for L-functions of
characters with negative discriminant, 2000; Bombieri, Counting points on curves over finite fields,
Sém. Bourbaki 430, 1973; van Frankenhuijsen, The Riemann hypothesis for function fields over a
finite field, 2008.
-/

namespace New

open Real Finset Data Module Submodule

/-- **Main inequality.** For the data `D` we have `m rem ≤ f a log⁵ b`.

The parameters `P` are a multiple `q₀` of `18480` and a prime `d ≡ q₀/2 - 1 mod q₀`. The scales are
integers with `(log b) ^ 100 ≤ x`, `x ^ 10⁶ ≤ x₁`, `x₁ ^ 10⁶ ≤ b` and
`log log b ≥ 10¹² P.constantBound`. -/
theorem star_inequality {P : Parameters} (D : Data P) :
    D.m * D.totalRemainder ≤ D.f * D.a * D.logB ^ 5 := by
  -- Choose many independent images of short integral forms, bound their covolume and index from
  -- above, and compare with the lower bound `integral_forms_long`.
  obtain ⟨h_dim_pos, t, ht_card, h_fill⟩ : 0 < D.targetDim ∧ ∃ t : Finset D.chosenGL,
      #t * finrank ℂ D.ramifiedSourceForms ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) ∧
      (1 - 4 / D.b ^ 2) * D.targetDim ≤ finrank ℂ ↥(⨆ g ∈ t, (D.normalizedPoincare g).range) :=
    D.enough_forms
  let loss : ℝ := D.f * D.a * D.logB ^ 4
  let logNormSq : ℝ := D.mainAmount - D.m * D.totalRemainder + loss
  let indexPerDim : ℝ := 10 * log (1 + 2 * D.b ^ 2) * D.errorUnit
  let short : Set D.ramifiedSourceForms :=
    {φ ∈ D.integralRamified | ∀ (g : D.chosenGL) (σ : ℂ ≃+* ℂ),
      (D.Θ 1 (D.normalizedPoincare g φ)).normSqAt σ ≤ exp logNormSq}
  have h_span : span ℂ short = ⊤ := D.span_short_integralRamified_eq_top
  -- The family: among the forms `D.normalizedPoincare g φ` with `g ∈ t` and `φ` short, a basis of
  -- their span.
  obtain ⟨n, y, h_indep, h_many, hy⟩ : ∃ (n : ℕ) (y : Fin n → D.targetForms),
      LinearIndependent ℂ y ∧ (1 - 4 / D.b ^ 2) * D.targetDim ≤ n ∧
      ∀ i : Fin n, ∃ g ∈ t, y i ∈ D.normalizedPoincare g '' short := by
    let images : Set D.targetForms := ⋃ g ∈ t, D.normalizedPoincare g '' short
    have span_eq : span ℂ images = ⨆ g ∈ t, (D.normalizedPoincare g).range := by
      simp only [images, span_iUnion₂, span_image, h_span, Submodule.map_top]
    obtain ⟨y, hy_mem, -, h_indep⟩ := exists_fun_fin_finrank_span_eq ℂ images
    refine ⟨finrank ℂ (span ℂ images), y, h_indep, by rwa [span_eq], fun i ↦ ?_⟩
    simpa only [images, Set.mem_iUnion, exists_prop] using hy_mem i
  have hn_le : (n : ℝ) ≤ D.targetDim := by simpa using h_indep.fintype_card_le_finrank
  -- Covolume: each form has squared length at most `exp logNormSq`.
  have h_cov : D.targetLattice.CovolumeLe y (n * logNormSq) := by
    refine TwistedLattice.covolumeLe_of_normSqAt_le fun i σ ↦ ?_
    obtain ⟨g, -, φ, ⟨-, hφ_short⟩, hφ_eq⟩ := hy i
    rw [normSqAt_targetLattice, ← hφ_eq]
    exact hφ_short g σ
  -- Index: each translate in `t` contributes `2 · errorUnit` per dimension of the source.
  have h_index : D.targetLattice.IndexLe y (D.targetDim * indexPerDim) := by
    have h_errorUnit_nonneg : 0 ≤ D.errorUnit := (HasLogBound.pos D).le
    have hy_int (i : Fin n) : ∃ g ∈ t, y i ∈ D.normalizedPoincare g '' D.integralRamified := by
      obtain ⟨g, hg, φ, ⟨hφ_int, -⟩, hφ_eq⟩ := hy i
      exact ⟨g, hg, φ, hφ_int, hφ_eq⟩
    refine (D.indexLe_normalizedPoincare t hy_int).mono ?_
    calc #t * finrank ℂ D.ramifiedSourceForms * (2 * D.errorUnit)
        ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) * (2 * D.errorUnit) := by grw [ht_card]
      _ = D.targetDim * indexPerDim := by ring
  -- Comparison: as `mainAmount + loss ≥ 0` and `n ≤ targetDim`, the terms `targetDim · mainAmount`
  -- cancel.
  have h_long :
      D.targetDim * (D.mainAmount - 3 * loss) ≤ n * logNormSq + 2 * (D.targetDim * indexPerDim) :=
    integral_forms_long h_indep h_many h_index h_cov
  have h_loss_pos : 0 < loss := HasLogBound.pos D
  have h_main : n * (D.mainAmount + loss) ≤ D.targetDim * (D.mainAmount + loss) :=
    mul_le_mul_of_nonneg_right hn_le (add_nonneg D.mainAmount_nonneg h_loss_pos.le)
  let err : ℝ := 4 * loss + 2 * indexPerDim
  have h_both : n * (D.m * D.totalRemainder) ≤ D.targetDim * err := by
    simp only [logNormSq, err] at h_long ⊢
    linarith [h_long, h_main]
  -- Divide by `n ≥ targetDim / 2 > 0`.
  have h_half : (D.targetDim : ℝ) ≤ n * 2 := by
    have h_share : 4 / D.b ^ 2 ≤ 2⁻¹ := D.le_of_hasLogBound
    calc (D.targetDim : ℝ) = (1 - 2⁻¹) * D.targetDim * 2 := by ring
      _ ≤ (1 - 4 / D.b ^ 2) * D.targetDim * 2 := by grw [h_share]
      _ ≤ n * 2 := by grw [h_many]
  have hn_pos : (0 : ℝ) < n :=
    pos_of_mul_pos_left ((Nat.cast_pos.2 h_dim_pos).trans_le h_half) zero_le_two
  -- The errors are of smaller order than `f a log⁵ b`.
  have h_err : |2 * err| ≤ D.f * D.a * D.logB ^ 5 := D.le_of_hasLogBound
  refine le_of_mul_le_mul_left ?_ hn_pos
  calc n * (D.m * D.totalRemainder) ≤ D.targetDim * |err| := by grw [h_both, ← le_abs_self]
    _ ≤ n * 2 * |err| := by grw [h_half]
    _ = n * |2 * err| := by rw [abs_mul, Nat.abs_ofNat, mul_assoc]
    _ ≤ n * (D.f * D.a * D.logB ^ 5) := by grw [h_err]

end New
