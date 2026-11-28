import New.Congruences.FitTwistsExist
import New.Determinant.AuxiliaryForms.SpanningForms
import New.OneLift.LiftVolumeHeight
import New.Reduction.IntegralTargetForms
import New.UpperBound.Size.ArchimedeanSize

/-!
# Theorem C: integral forms are long

The main result `New.Data.integral_forms_long` bounds from below the covolume plus twice the index
of a family of target forms that spans almost all of the target. The target forms are a twisted
lattice, and the bound follows from `New.TwistedLattice.covolume_add_index_nonneg` with four inputs:
auxiliary forms that complete a family to a basis, a family of twists `ξ_ι`, the injectivity of the
lifts `Θ_ξ`, and the height of `Z(1) / Z(ξ_ι)`.

In comments, `d` is the dimension `D.targetDim` of the target `D.targetForms`, the space of good
forms on `Y₀ = D.spaceY 0`. The letters `x, x₁, b, a, m, k, t, f` are the numbers `D.x`, `D.x₁`, …
of the data `D`; inequalities between them come from `New.Data.le_of_hasLogBound`.

Notions from other files:
* `D.targetLattice`: the target forms as a twisted lattice, with the lifts `Θ_ξ = D.Θ ξ` indexed by
  the `m`-fold twists `ξ`; the modulus `Q(ξ)` has norm `ξ.normQ`.
* `D.chainDeterminant ξ` is `Z(ξ) = det (Θ_ξ* Θ_ξ)`, and `D.liftDeterminant ξ j` is `Z_j(ξ ^ j)`,
  the same determinant for the `j`-th single lift.
* `HeightLe c y`: the family `y` of complex numbers, one for each pair `ι` of a prime `l` and an
  isomorphism `ℂ ≃ ℚ̄_l` (`PrimePadicIso`), has height at most `c`.
* `D.HasSmallRatios θ`: the `m`-fold twists `ξ_ι = θ ι` have `Nm Q(ξ_ι)` prime to the prime of `ι`
  and inverse ratios of Hecke values of height at most `x₁`.
-/

namespace New.Data

open Submodule Module Real Finset Matrix LevelPlaces.LevelForm LinearMap

variable {P : Parameters} {D : Data P}

/-! ### Auxiliary forms -/

variable (D) in
/-- A target form `y` is auxiliary for the scalars `γ ϑ`, one for each `m`-fold twist `ϑ`, if its
lifts `γ ϑ • D.Θ ϑ y` are integral at primes not dividing `ϑ.normQ` and every conjugate of its lift
`D.Θ 1 y` has squared norm at most `exp (2 x₁² b²)`. -/
structure IsAuxiliaryForm (γ : D.MFoldTwist → ℂ) (y : D.targetForms) : Prop where
  /-- The form `γ ϑ • Θ_ϑ y` is integral at `ι : ℂ ≃ ℚ̄_l` whenever the norm `ϑ.normQ` of the
  modulus of `ϑ` is prime to `l = ι.1`. -/
  smul_lift_mem_integralForms (ι : PrimePadicIso) (ϑ : D.MFoldTwist)
    (hϑ : Nat.Coprime ι.1 ϑ.normQ) : γ ϑ • D.Θ ϑ y ∈ integralForms ι.place
  /-- The conjugate of `Θ₁ y` by each automorphism `σ` of `ℂ` has squared norm at most
  `exp (2 x₁² b²)`. -/
  normSqAt_lift_le (σ : ℂ ≃+* ℂ) : (D.Θ 1 y).normSqAt σ ≤ exp (2 * D.x₁ ^ 2 * D.b ^ 2)

variable (D) in
/-- The normalized scalars for the auxiliary forms give integral lifts, span the target,
and have uniformly bounded inverse squared norm at any family of twists with small ratios. -/
theorem exists_span_isAuxiliaryForm_eq_top :
    ∃ γ : D.MFoldTwist → ℂ, (∀ ϑ, γ ϑ ≠ 0) ∧ γ 1 = 1 ∧
      (∀ {θ : PrimePadicIso → D.MFoldTwist}, D.HasSmallRatios θ →
        HeightLe D.b fun ι ↦ ((‖γ (θ ι)‖ : ℂ) ^ 2)⁻¹) ∧
      span ℂ {y : D.targetForms | D.IsAuxiliaryForm γ y} = ⊤ := by
  obtain ⟨scalar, h_modulus, h_span⟩ := D.exists_span_short_lifts_eq_top
  have hM : D.HasAbsUpToNormPower (fun ϑ ↦ (scalar ϑ : ℂ))
      (∏ ij ∈ range D.m ×ˢ range D.m, D.turnRatio ij.1 ij.2) := by
    simpa only [prod_product] using h_modulus
  refine ⟨fun ϑ ↦ scalar ϑ / scalar 1,
    fun ϑ ↦ div_ne_zero (scalar ϑ).ne_zero (scalar 1).ne_zero, div_self (scalar 1).ne_zero, ?_, ?_⟩
  · intro θ hθ
    have h := hM.heightLe_norm_div hθ isRamifiedRatio_turnRatio_of_mem
    have h_cost : 2 * (D.m * D.m * (D.t * D.x₁)) ≤ D.b := D.le_of_hasLogBound
    refine (h.pow 2).mono (by simpa using h_cost) fun ι ↦ le_of_eq ?_
    rw [Pi.pow_apply, ← inv_pow, ← Complex.ofReal_inv, ← norm_inv, inv_div]
  -- The projection is onto, so it maps a spanning set to a spanning set.
  have h_onto : Submodule.map (D.goodProjTranslate 1) ⊤ = ⊤ := by
    simp [range_smul, NeZero.ne, End.one_eq_id]
  rw [← h_span, ← span_image] at h_onto
  refine eq_top_mono (span_mono ?_) h_onto
  rintro _ ⟨ψ, ⟨h_int, h_short⟩, rfl⟩
  have h_exponent_le : D.x ^ 99 + D.x ^ 202 * D.b ^ 2 ≤ 2 * D.x₁ ^ 2 * D.b ^ 2 :=
    D.le_of_hasLogBound
  refine ⟨fun ι ϑ hϑ ↦ ?_, fun σ ↦ ?_⟩
  · exact goodProjTranslate_mem_integralForms ι.place (h_int ϑ ι.1 ι.place hϑ) 1
  · exact (normSqAt_goodProjTranslate_le (h_short σ)).trans (exp_le_exp.2 h_exponent_le)

/-- The cost of completing a family to a basis: if `n ≥ (1 - 4 / b²) d` and `d = n + n'`, where
`d = D.targetDim`, then `n' (2 x₁² b² + b) ≤ d b`. That is, `n'` forms, each costing `2 x₁² b² + b`,
cost at most `d b` in total. -/
lemma mul_completion_cost_le {n n' : ℕ} (hn : (1 - 4 / D.b ^ 2) * D.targetDim ≤ n)
    (h_card : D.targetDim = n + n') :
    n' * (2 * D.x₁ ^ 2 * D.b ^ 2 + D.b) ≤ D.targetDim * D.b := by
  -- There are at most `4 d / b²` forms, and the factor `b⁻²` cancels the `b²` in their cost.
  have hb : 0 < D.b := HasLogBound.pos D
  have h_dim : (D.targetDim : ℝ) = n + n' := mod_cast h_card
  have h_few : (n' : ℝ) ≤ 4 / D.b ^ 2 * D.targetDim := by linarith
  have h_cost : 4 * (2 * D.x₁ ^ 2 + D.b⁻¹) ≤ D.b := D.le_of_hasLogBound
  calc n' * (2 * D.x₁ ^ 2 * D.b ^ 2 + D.b)
      ≤ 4 / D.b ^ 2 * D.targetDim * (2 * D.x₁ ^ 2 * D.b ^ 2 + D.b) := by gcongr
    _ = D.targetDim * (4 * (2 * D.x₁ ^ 2 + D.b⁻¹)) := by field
    _ ≤ D.targetDim * D.b := by gcongr

/-! ### The inverse ratio -/

variable (D) in
/-- **Single lifts at good twists.** There is a family of `m`-fold twists `ξ_ι = θ ι`, one for each
prime `l` and `ι : ℂ ≃ ℚ̄_l`, with small ratios such that for `1 ≤ j ≤ m` the family
`Z_j(1) / Z_j(ξ_ι ^ j)` has height at most `d (f a log⁴ b / m - k D.directionAmount)`. -/
theorem exists_hasSmallRatios_heightLe_liftDeterminant_div :
    ∃ θ : PrimePadicIso → D.MFoldTwist, D.HasSmallRatios θ ∧ ∀ j ∈ Icc 1 D.m,
      HeightLe (D.targetDim * (D.f * D.a * D.logB ^ 4 / D.m - D.k * D.directionAmount))
        fun ι : PrimePadicIso ↦ D.liftDeterminant 1 j / D.liftDeterminant (θ ι) j := by
  -- Every regular family serves.
  obtain ⟨θ, hθ⟩ := exists_isRegularFamily D
  refine ⟨θ, hθ.toHasSmallRatios, fun j hj ↦ ?_⟩
  have hk : (D.k : ℝ) ≠ 0 := (HasLogBound.pos D).ne'
  have h_budget : D.k * (D.logB * D.denominatorBudget) = D.f * D.a * D.logB ^ 4 / D.m := by
    rw [denominatorBudget, errorUnit]
    field_simp
  rw [← h_budget, ← mul_sub]
  exact heightLe_liftDeterminant_ratio hθ ⟨j, mem_Icc.1 hj⟩

/-- **The inverse ratio.** Let the family of `m`-fold twists `ξ_ι = θ ι`, one for each
`ι : ℂ ≃ ℚ̄_l`, have small ratios, and suppose that for `1 ≤ j ≤ m` the family
`D.liftDeterminant 1 j / D.liftDeterminant ξ_ι j` of quotients of Gram determinants of the `j`-th
single lift has height at most `d (f a log⁴ b / m - k D.directionAmount)`. Then the family
`Z(1) / Z(ξ_ι)` has height at most `d (b + f a log⁴ b - D.mainAmount)`, where
`D.mainAmount = m k D.directionAmount`. -/
lemma heightLe_chainDeterminant_one_div {θ : PrimePadicIso → D.MFoldTwist} (hθ : D.HasSmallRatios θ)
    (h_single : ∀ j ∈ Icc 1 D.m,
      HeightLe (D.targetDim * (D.f * D.a * D.logB ^ 4 / D.m - D.k * D.directionAmount))
        fun ι : PrimePadicIso ↦ D.liftDeterminant 1 j / D.liftDeterminant (θ ι) j) :
    HeightLe (D.targetDim * (D.b + D.f * D.a * D.logB ^ 4 - D.mainAmount))
      fun ι : PrimePadicIso ↦ D.chainDeterminant (1 : D.MFoldTwist) / D.chainDeterminant (θ ι) := by
  -- Add the heights of the factors of `Z(1) / Z(ξ_ι)`.
  obtain ⟨c, h_scalar, h_factor⟩ := D.exists_chainDeterminant_eq_norm_pow_mul_prod
  -- The `m` bounds for the single lifts add up, as `m k D.directionAmount = D.mainAmount`.
  have h_lifts : HeightLe (D.targetDim * (D.f * D.a * D.logB ^ 4 - D.mainAmount))
      (∏ j ∈ Icc 1 D.m, fun ι : PrimePadicIso ↦
        D.liftDeterminant 1 j / D.liftDeterminant (θ ι) j) := by
    have hm : (D.m : ℝ) ≠ 0 := (HasLogBound.pos D).ne'
    refine (HeightLe.prod h_single).mono (le_of_eq ?_) fun _ ↦ le_rfl
    rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mainAmount]
    field_simp
  refine (((h_scalar hθ).pow D.targetDim).mul h_lifts).mono (le_of_eq (by ring)) fun ι ↦ le_of_eq ?_
  rw [h_factor 1, h_factor (θ ι), Pi.mul_apply, Pi.pow_apply, Finset.prod_apply, norm_div,
    Complex.ofReal_div, div_pow, prod_div_distrib, mul_div_mul_comm]

/-! ### The lower bound -/

/-- **Theorem C: integral forms are long.** Let `y_1, …, y_n` be independent target forms with
`n ≥ (1 - 4 / b²) d`. Suppose that `y` has index at most `δ`: there are `δ_l ≥ 0` with
`∑ δ_l log l ≤ δ` such that for each `ι` an `ι`-integral matrix, with determinant of valuation at
most `δ_l`, takes `y` to forms integral at `ι`. Suppose that `y` has covolume at most `c`: the Gram
determinant of every conjugate of the untwisted lift `D.Θ 1 y` is at most `exp c` in absolute value.
Then `c + 2 δ ≥ d (D.mainAmount - 3 f a log⁴ b)`. -/
theorem integral_forms_long {n : ℕ} {y : Fin n → D.targetForms} {δ c : ℝ}
    (hy : LinearIndependent ℂ y) (hn : (1 - 4 / D.b ^ 2) * D.targetDim ≤ n)
    (hδ : D.targetLattice.IndexLe y δ) (hc : D.targetLattice.CovolumeLe y c) :
    D.targetDim * (D.mainAmount - 3 * (D.f * D.a * D.logB ^ 4)) ≤ c + 2 * δ := by
  -- Complete `y` to a basis by auxiliary forms `z` and take a twist for each prime.
  obtain ⟨θ, hθ, h_single⟩ := D.exists_hasSmallRatios_heightLe_liftDeterminant_div
  obtain ⟨γ, hγ_ne, -, hγ_height, h_span⟩ := D.exists_span_isAuxiliaryForm_eq_top
  obtain ⟨n', z, hz, h_indep, h_card⟩ := exists_extend_basis_of_span_eq_top hy h_span
  have hz_aux (i : Fin n') : D.IsAuxiliaryForm γ (z i) := hz i
  have hz_int (i : Fin n') (ι : PrimePadicIso) (ϑ : D.MFoldTwist)
      (hϑ : Nat.Coprime ι.1 ϑ.normQ) : γ ϑ • D.Θ ϑ (z i) ∈ integralForms ι.place :=
    (hz_aux i).smul_lift_mem_integralForms ι ϑ hϑ
  have hz_short (i : Fin n') (σ : ℂ ≃+* ℂ) :
      D.targetLattice.normSqAt (z i) σ ≤ exp (2 * D.x₁ ^ 2 * D.b ^ 2) :=
    (normSqAt_targetLattice (z i) σ).trans_le ((hz_aux i).normSqAt_lift_le σ)
  have h_volume : HeightLe (D.targetDim * (D.b + D.f * D.a * D.logB ^ 4 - D.mainAmount))
      fun ι : PrimePadicIso ↦ D.targetLattice.volume 1 / D.targetLattice.volume (θ ι) := by
    simp only [volume_targetLattice]
    exact heightLe_chainDeterminant_one_div hθ h_single
  have h_nonneg : 0 ≤ c + 2 * δ + n' * (2 * D.x₁ ^ 2 * D.b ^ 2 + D.b) +
      D.targetDim * (D.b + D.f * D.a * D.logB ^ 4 - D.mainAmount) :=
    TwistedLattice.covolume_add_index_nonneg injective_lift_targetLattice h_indep h_card hθ.coprime
      hc hδ hγ_ne hz_int hz_short (hγ_height hθ) h_volume
  have h_completion : n' * (2 * D.x₁ ^ 2 * D.b ^ 2 + D.b) ≤ D.targetDim * D.b :=
    mul_completion_cost_le hn h_card
  -- The two terms `d b` are absorbed in the error.
  have h_b_le_error : D.targetDim * D.b ≤ D.targetDim * (D.f * D.a * D.logB ^ 4) :=
    mul_le_mul_of_nonneg_left D.le_of_hasLogBound D.targetDim.cast_nonneg
  linarith

end New.Data
