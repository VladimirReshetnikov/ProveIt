import OAI.Combinatorics.Progressions.Nilpotent.BracketArrayEquation
import OAI.Combinatorics.Progressions.Nilpotent.BracketStepBudget
import OAI.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem projected_lift_residual_eq {σ μ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (b : Basis μ ℝ L) (w : μ → ℕ) {j : ℕ} (hj : j ≠ 1)
    (S : VectorPolynomial σ ℚ L) (k : L) (hk : basisGradeProjection b w 1 k = k) :
    map ((basisGradeProjection b w j).restrictScalars ℚ) (S - monomial 0 k) =
      map ((basisGradeProjection b w j).restrictScalars ℚ) S := by
  have hz := basisGradeProjection_other b w hj k
  rw [hk] at hz
  rw [map_sub, map_monomial]
  change map ((basisGradeProjection b w j).restrictScalars ℚ) S -
    monomial 0 (basisGradeProjection b w j k) = _
  rw [hz]
  simp only [monomial, TensorProduct.tmul_zero, sub_zero]

variable {σ κ ι μ L : Type*} [Fintype κ] [Fintype ι] [Fintype μ]
  [LieRing L] [LieAlgebra ℚ L] {V : Submodule ℚ L}

omit [Fintype μ] in
theorem projected_lift_array_homogeneous (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) {j : ℕ} (hj : 2 ≤ j)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ t, S t ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) :
    ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 →
      coefficients (liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α = 0 := by
  intro α hα
  apply liftQuotientArray_coefficient_eq_zero
  intro t
  rw [projected_lift_residual_eq (b.baseChange ℝ) w (by omega) (S t) _ (hk t)]
  exact shifted_one_projection_homogeneous (b.baseChange ℝ) w (S t) (hS t) (by omega) α hα

theorem projected_lift_array_bound (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) {j H : ℕ} (hj : 2 ≤ j)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    (hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ t α, ‖(b.baseChange ℝ).equivFun (coefficients (S t) α)‖ ≤ M / monomialScale T α) :
    ∀ α, ‖coefficients (liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (S t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α‖ ≤
      (((Fintype.card μ : ℝ) + 1) * (H + 1)) * M / monomialScale T α := by
  intro α
  let C : ℝ := ((Fintype.card μ : ℝ) + 1) * (H + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply liftQuotientArray_norm_bound f _ α (div_nonneg (mul_nonneg hC hM) (monomialScale_pos T hT α).le)
  intro t
  rw [projected_lift_residual_eq (b.baseChange ℝ) w (by omega) (S t) _ (hk t), coefficients_map]
  change ‖realQuotientCoordinateMap f
    (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α))‖ ≤ C * M / monomialScale T α
  calc
    _ ≤ C * ‖(b.baseChange ℝ).equivFun
        (basisGradeProjection (b.baseChange ℝ) w j (coefficients (S t) α))‖ :=
      realQuotientCoordinateMap_norm_bound b f hf _
    _ ≤ C * ‖(b.baseChange ℝ).equivFun (coefficients (S t) α)‖ :=
      mul_le_mul_of_nonneg_left (basisCoordinateProjection_norm_le (b.baseChange ℝ) {n | w n = j} _) hC
    _ ≤ C * (M / monomialScale T α) := mul_le_mul_of_nonneg_left (hS t α) hC
    _ = C * M / monomialScale T α := (mul_div_assoc C M (monomialScale T α)).symm

theorem projected_lift_array_grid (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) {j : ℕ} (hj : 2 ≤ j)
    (hk : ∀ t, basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] k t) =
      (1 : ℝ) ⊗ₜ[ℚ] k t)
    (l : ℕ) (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hR : ∀ t α, (b.baseChange ℝ).equivFun (coefficients (R t) α) ∈ realDenominatorGrid l) :
    ∀ α, coefficients (liftQuotientArray f (fun t =>
        map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
          (R t - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] k t)))) α ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  intro α
  apply liftQuotientArray_grid
  intro t
  rw [projected_lift_residual_eq (b.baseChange ℝ) w (by omega) (R t) _ (hk t), coefficients_map]
  apply realQuotientCoordinateMap_grid b f l
  exact basisCoordinateProjection_real_grid (b.baseChange ℝ) {n | w n = j} l _ (hR t α)

theorem liftQuotientArray_map_neg (f : Basis ι ℚ (L ⧸ V))
    (π : (ℝ ⊗[ℚ] L) →ₗ[ℚ] (ℝ ⊗[ℚ] L))
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    liftQuotientArray f (fun t => map π (-(R t))) = -liftQuotientArray f (fun t => map π (R t)) := by
  simp only [map_neg]
  exact liftQuotientArray_neg f _

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {L μ ι σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] {V : Submodule ℚ L}

theorem projected_polynomial_coefficient_bound (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (j : ℕ) {H : ℕ}
    (hf : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : CoefficientBound (b.baseChange ℝ) T M P)
    (α : σ →₀ ℕ) :
    ‖realQuotientCoordinateMap f (coefficients
      (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P) α)‖ ≤
      (((Fintype.card μ : ℝ) + 1) * (H + 1)) * M / monomialScale T α := by
  rw [coefficients_map]
  let C : ℝ := ((Fintype.card μ : ℝ) + 1) * (H + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb := (coefficientBound_iff_norm (b.baseChange ℝ) T hT hM P).mp hP α
  calc
    _ ≤ C * ‖(b.baseChange ℝ).equivFun
        (basisGradeProjection (b.baseChange ℝ) w j (coefficients P α))‖ :=
      realQuotientCoordinateMap_norm_bound b f hf _
    _ ≤ C * ‖(b.baseChange ℝ).equivFun (coefficients P α)‖ :=
      mul_le_mul_of_nonneg_left (basisCoordinateProjection_norm_le (b.baseChange ℝ) {z | w z = j} _) hC
    _ ≤ C * (M / monomialScale T α) := mul_le_mul_of_nonneg_left hb hC
    _ = _ := by ring

theorem projected_polynomial_coefficient_grid (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (j l : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : CoefficientGrid (b.baseChange ℝ) l P)
    (α : σ →₀ ℕ) :
    realQuotientCoordinateMap f (coefficients
      (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P) α) ∈
      realDenominatorGrid (matrixDenominator (quotientCoordinateMatrix b f) * l) := by
  rw [coefficients_map]
  apply realQuotientCoordinateMap_grid b f l
  exact basisCoordinateProjection_real_grid (b.baseChange ℝ) {z | w z = j} l _ (hP α)

theorem uniform_current_layer_inputs_from_ambient (b : Basis μ ℚ L) (w : μ → ℕ)
    (f : Basis ι ℚ (L ⧸ V)) (j : ℕ) {H l : ℕ}
    (hl : 0 < l) (hf : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hambient : (Fintype.card μ : ℝ) ≤ p)
    (hquotient : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i))
    (hrational : ∀ i, CoefficientGrid (b.baseChange ℝ) l (rational i)) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp (bracketConstructionBudget p) ∧
      (∀ i α, ‖realQuotientCoordinateMap f (coefficients
        (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
          Real.exp (bracketConstructionBudget p) / (T i * monomialScale T α)) ∧
      ∀ i α, realQuotientCoordinateMap f (coefficients
        (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
          realDenominatorGrid n := by
  let n := matrixDenominator (quotientCoordinateMatrix b f) * l
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos _) hl
  obtain ⟨_, _, hdenCap, hnormCap⟩ := bracket_construction_budget_bounds hp
  have hD := matrixDenominator_le_exp_power (quotientCoordinateMatrix b f) hp 1 hquotient hambient
    (fun i z => (show (((quotientCoordinateMatrix b f i z).den) : ℝ) ≤ H from Nat.cast_le.mpr (hf i z).2).trans
      (hHp.trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))))
  have hnbound : (n : ℝ) ≤ Real.exp (bracketConstructionBudget p) := by
    calc
      _ = (matrixDenominator (quotientCoordinateMatrix b f) : ℝ) * (l : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp p :=
        mul_le_mul hD hlp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdenCap
  have hfactor : (((Fintype.card μ : ℝ) + 1) * (H + 1)) * Real.exp p ≤
      Real.exp (bracketConstructionBudget p) := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp p :=
        mul_le_mul_of_nonneg_right (current_layer_coordinate_factor_bound hp _ H hambient hHp) (Real.exp_nonneg _)
      _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hnormCap
  refine ⟨n, hn, hnbound, ?_, fun i α => projected_polynomial_coefficient_grid b w f j l _ (hrational i) α⟩
  intro i α
  have h := projected_polynomial_coefficient_bound b w f j hf T hT
    (div_nonneg (Real.exp_nonneg p) (hT i).le) (small i) (hsmall i) α
  calc
    _ ≤ (((Fintype.card μ : ℝ) + 1) * (H + 1)) * (Real.exp p / T i) / monomialScale T α := h
    _ = ((((Fintype.card μ : ℝ) + 1) * (H + 1)) * Real.exp p) / (T i * monomialScale T α) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hfactor (mul_nonneg (hT i).le (monomialScale_pos T hT α).le)

end Erdos3

end

end OAI
