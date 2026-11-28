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
/-- **Auxiliary forms.** There are an integer `e` and numbers `γ ϑ ≠ 0`, for the `m`-fold twists
`ϑ`, such that `γ 1 = 1`, the absolute value of `γ ϑ` is the norm `ϑ.normQ` of the modulus of `ϑ` to
the power `e / 2` times the numbers `D.turnRatio i j ϑ` for `0 ≤ i, j < m`, and the space
`D.targetForms` is spanned by the forms `y` that are auxiliary for `γ`: each lift `γ ϑ • D.Θ ϑ y` is
integral at the primes not dividing `ϑ.normQ`, and every conjugate of `D.Θ 1 y` has squared norm at
most `exp (2 x₁² b²)`, for the scales `x₁`, `b` of `D`. -/
theorem exists_span_isAuxiliaryForm_eq_top :
    ∃ (e : ℤ) (γ : D.MFoldTwist → ℂ),
      (∀ ϑ : D.MFoldTwist, γ ϑ ≠ 0) ∧
      γ 1 = 1 ∧
      (∀ ϑ : D.MFoldTwist, ‖γ ϑ‖ = (ϑ.normQ : ℝ) ^ (e / 2 : ℝ) *
        ∏ i ∈ Finset.range D.m, ∏ j ∈ Finset.range D.m, D.turnRatio i j ϑ) ∧
      span ℂ {y : D.targetForms | D.IsAuxiliaryForm γ y} = ⊤ := by
  -- Apply `D.goodProjTranslate 1`, a multiple of the projection to the target, to the spanning
  -- forms on `Y₀` with short lifts. The lifts stay integral, and the logarithms of their squared
  -- norms are at most `x ^ 99 + x ^ 202 b²`.
  obtain ⟨scalar, h_modulus, h_span⟩ := D.exists_span_short_lifts_eq_top
  set F : D.MFoldTwist → ℝ := ∏ i ∈ Finset.range D.m, ∏ j ∈ Finset.range D.m, D.turnRatio i j
  have hF (ϑ : D.MFoldTwist) :
      F ϑ = ∏ i ∈ Finset.range D.m, ∏ j ∈ Finset.range D.m, D.turnRatio i j ϑ := by
    simp only [F, Finset.prod_apply]
  have hF_one : F 1 = 1 := by
    rw [hF]
    exact prod_eq_one fun i hi ↦ prod_eq_one fun j hj ↦
      (isRamifiedRatio_turnRatio (mem_range.1 hi) (mem_range.1 hj)).apply_one
  have hF_nonneg (ϑ : D.MFoldTwist) : 0 ≤ F ϑ := by
    rw [hF]
    exact prod_nonneg fun i hi ↦ prod_nonneg fun j hj ↦
      (isRamifiedRatio_turnRatio (mem_range.1 hi) (mem_range.1 hj)).nonneg ϑ
  obtain ⟨e, he⟩ : ∃ e : ℤ, ∀ ϑ : D.MFoldTwist,
      ‖(scalar ϑ / scalar 1 : ℂ)‖ = (ϑ.normQ : ℝ) ^ (e / 2 : ℝ) * F ϑ :=
    h_modulus.exists_norm_div_eq hF_one hF_nonneg (scalar 1).ne_zero
  have hγ_norm (ϑ : D.MFoldTwist) : ‖(scalar ϑ / scalar 1 : ℂ)‖ = (ϑ.normQ : ℝ) ^ (e / 2 : ℝ) *
      ∏ i ∈ Finset.range D.m, ∏ j ∈ Finset.range D.m, D.turnRatio i j ϑ := by
    rw [he, hF]
  refine ⟨e, fun ϑ ↦ scalar ϑ / scalar 1,
    fun ϑ ↦ div_ne_zero (scalar ϑ).ne_zero (scalar 1).ne_zero, div_self (scalar 1).ne_zero,
    hγ_norm, ?_⟩
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

/-- Let `ξ_ι = θ ι` be a family of `m`-fold twists, one for each `ι : ℂ ≃ ℚ̄_l`. Assume the family
has small ratios: `Nm Q(ξ_ι) = (θ ι).normQ` is prime to `l`, and the inverse ratios of Hecke
L-values have height at most `x₁`. Let `e` be an integer. Then the inverse of the product of
`Nm Q(ξ_ι) ^ (e / 2)` and the `m²` numbers `D.turnRatio i j ξ_ι` (for `i, j < m`) has height at most
`m² t x₁`. -/
lemma HasSmallRatios.heightLe_inv_rpow_mul_prod_turnRatio {θ : PrimePadicIso → D.MFoldTwist}
    (hθ : D.HasSmallRatios θ) (e : ℤ) :
    HeightLe (D.m * D.m * (D.t * D.x₁)) fun ι : PrimePadicIso ↦
      ((((θ ι).normQ : ℝ) ^ (e / 2 : ℝ) *
        ∏ i ∈ Finset.range D.m, ∏ j ∈ Finset.range D.m, D.turnRatio i j (θ ι) : ℝ) : ℂ)⁻¹ := by
  refine (hθ.heightLe_inv_rpow_mul_prod e isRamifiedRatio_turnRatio_of_mem).mono
    (le_of_eq (by simp)) fun ι ↦ le_of_eq ?_
  rw [prod_product]

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

variable (D) in
/-- The inverted factorisation of the Gram determinant `D.chainDeterminant ϑ` of the lift `D.Θ ϑ`:
for an integer `e` independent of the `m`-fold twist `ϑ`, the quotient
`D.chainDeterminant 1 / D.chainDeterminant ϑ` is the product of the same quotients for the Gram
determinants `D.liftDeterminant` of the single lifts, times the `D.targetDim`-th power of the
inverse of a scalar. The scalar is the norm `ϑ.normQ` of the modulus of `ϑ` to the power `e / 2`,
times the numbers `D.quotientRatio i j ϑ` for `1 ≤ i < j ≤ m`, each the product of `D.t` ratios of
Hecke L-values of the character `D.untwistedLiftChar j / D.untwistedLiftChar i` at `ϑ ^ (j - i)`;
the characters `D.untwistedLiftChar j` of `U(1)(𝔸)` are those of the lifts at the trivial twist. -/
lemma exists_chainDeterminant_one_div_eq :
    ∃ e : ℤ, ∀ ϑ : D.MFoldTwist,
      D.chainDeterminant 1 / D.chainDeterminant ϑ =
        (((ϑ.normQ : ℝ) ^ (e / 2 : ℝ) *
            ∏ i ∈ Ioc 0 D.m, ∏ j ∈ Ioc i D.m, D.quotientRatio i j ϑ : ℝ) : ℂ)⁻¹ ^ D.targetDim *
          ∏ j ∈ Icc 1 D.m, D.liftDeterminant 1 j / D.liftDeterminant ϑ j := by
  obtain ⟨e, h_factor⟩ := D.exists_chainDeterminant_pos_and_div_chainDeterminant_one_eq
  refine ⟨e, fun ϑ ↦ ?_⟩
  obtain ⟨-, -, h_ratio⟩ := h_factor ϑ
  rw [← inv_div, h_ratio, mul_inv, inv_pow, ← prod_inv_distrib]
  simp only [inv_div]

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
  obtain ⟨e, h_factor⟩ := D.exists_chainDeterminant_one_div_eq
  let scalar (ϑ : D.MFoldTwist) : ℝ := (ϑ.normQ : ℝ) ^ (e / 2 : ℝ) *
    ∏ i ∈ Ioc 0 D.m, ∏ j ∈ Ioc i D.m, D.quotientRatio i j ϑ
  -- The power of `Nm Q` costs nothing, and each of the at most `m² t` inverse ratios of Hecke
  -- values costs `x₁`.
  have h_scalar : HeightLe D.b fun ι : PrimePadicIso ↦ (scalar (θ ι) : ℂ)⁻¹ := by
    have h_cost : D.m * D.m * (D.t * D.x₁) ≤ D.b := D.le_of_hasLogBound
    exact (hθ.heightLe_inv_rpow_mul_prod_quotientRatio e).mono h_cost fun _ ↦ le_rfl
  -- The `m` bounds for the single lifts add up, as `m k D.directionAmount = D.mainAmount`.
  have h_lifts : HeightLe (D.targetDim * (D.f * D.a * D.logB ^ 4 - D.mainAmount))
      (∏ j ∈ Icc 1 D.m, fun ι : PrimePadicIso ↦
        D.liftDeterminant 1 j / D.liftDeterminant (θ ι) j) := by
    have hm : (D.m : ℝ) ≠ 0 := (HasLogBound.pos D).ne'
    refine (HeightLe.prod h_single).mono (le_of_eq ?_) fun _ ↦ le_rfl
    rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mainAmount]
    field_simp
  refine ((h_scalar.pow D.targetDim).mul h_lifts).mono (le_of_eq (by ring)) fun ι ↦ le_of_eq ?_
  rw [h_factor, Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]

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
  obtain ⟨e, γ, hγ_ne, -, hγ_norm, h_span⟩ := D.exists_span_isAuxiliaryForm_eq_top
  obtain ⟨n', z, hz, h_indep, h_card⟩ := exists_extend_basis_of_span_eq_top hy h_span
  have hz_aux (i : Fin n') : D.IsAuxiliaryForm γ (z i) := hz i
  have hz_int (i : Fin n') (ι : PrimePadicIso) (ϑ : D.MFoldTwist)
      (hϑ : Nat.Coprime ι.1 ϑ.normQ) : γ ϑ • D.Θ ϑ (z i) ∈ integralForms ι.place :=
    (hz_aux i).smul_lift_mem_integralForms ι ϑ hϑ
  have hz_short (i : Fin n') (σ : ℂ ≃+* ℂ) :
      D.targetLattice.normSqAt (z i) σ ≤ exp (2 * D.x₁ ^ 2 * D.b ^ 2) :=
    (normSqAt_targetLattice (z i) σ).trans_le ((hz_aux i).normSqAt_lift_le σ)
  -- `|γ| ^ (-2)` is a power of `Nm Q` times `2 m² t` inverse ratios of Hecke values.
  have h_scalar : HeightLe D.b fun ι : PrimePadicIso ↦ ((‖γ (θ ι)‖ : ℂ) ^ 2)⁻¹ := by
    have h_cost : 2 * (D.m * D.m * (D.t * D.x₁)) ≤ D.b := D.le_of_hasLogBound
    refine ((hθ.heightLe_inv_rpow_mul_prod_turnRatio e).pow 2).mono (mod_cast h_cost)
      fun ι ↦ le_of_eq ?_
    rw [hγ_norm, Pi.pow_apply, inv_pow]
  have h_volume : HeightLe (D.targetDim * (D.b + D.f * D.a * D.logB ^ 4 - D.mainAmount))
      fun ι : PrimePadicIso ↦ D.targetLattice.volume 1 / D.targetLattice.volume (θ ι) := by
    simp only [volume_targetLattice]
    exact heightLe_chainDeterminant_one_div hθ h_single
  have h_nonneg : 0 ≤ c + 2 * δ + n' * (2 * D.x₁ ^ 2 * D.b ^ 2 + D.b) +
      D.targetDim * (D.b + D.f * D.a * D.logB ^ 4 - D.mainAmount) :=
    TwistedLattice.covolume_add_index_nonneg injective_lift_targetLattice h_indep h_card hθ.coprime
      hc hδ hγ_ne hz_int hz_short h_scalar h_volume
  have h_completion : n' * (2 * D.x₁ ^ 2 * D.b ^ 2 + D.b) ≤ D.targetDim * D.b :=
    mul_completion_cost_le hn h_card
  -- The two terms `d b` are absorbed in the error.
  have h_b_le_error : D.targetDim * D.b ≤ D.targetDim * (D.f * D.a * D.logB ^ 4) :=
    mul_le_mul_of_nonneg_left D.le_of_hasLogBound D.targetDim.cast_nonneg
  linarith

end New.Data
