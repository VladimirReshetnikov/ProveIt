import OAI.Combinatorics.Progressions.Polynomial.CurrentPolynomialDerivativeRemoval
import OAI.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

variable {σ κ K L : Type*} [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L]

noncomputable def basisPolynomialLift (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    K →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) := b.constr ℝ S

@[simp] theorem basisPolynomialLift_basis (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : κ) :
    basisPolynomialLift b S (b k) = S k := b.constr_basis ℝ S k

variable [Fintype κ]

theorem basisPolynomialLift_coefficients (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (x : K) (α : σ →₀ ℕ) :
    coefficients (basisPolynomialLift b S x) α =
      ∑ k, b.equivFun x k • coefficients (S k) α := by
  classical
  change realCoefficient α (b.constr ℝ S x) = _
  rw [Basis.constr_apply_fintype (S := ℝ)]
  simp only [map_sum, map_smul, realCoefficient_apply]

theorem realLinearPolynomial_mem_of_basis (b : Basis κ ℝ K)
    (S : K →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (W : (σ →₀ ℕ) → Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (S (b k)) α ∈ W α) (x : K) (α : σ →₀ ℕ) :
    coefficients (S x) α ∈ W α := by
  classical
  change ((realCoefficient α).comp S) x ∈ W α
  rw [← b.sum_repr x, map_sum]
  apply (W α).sum_mem
  intro k _
  rw [map_smul]
  exact (W α).smul_mem _ (h k α)

theorem basisPolynomialLift_mem (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (W : (σ →₀ ℕ) → Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (S k) α ∈ W α) (x : K) (α : σ →₀ ℕ) :
    coefficients (basisPolynomialLift b S x) α ∈ W α :=
  realLinearPolynomial_mem_of_basis b (basisPolynomialLift b S) W
    (fun k α => by rw [basisPolynomialLift_basis]; exact h k α) x α

theorem basisPolynomialLift_residual (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (I : K →ₗ[ℝ] ℝ ⊗[ℚ] L)
    (W : Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (S k - monomial 0 (I (b k))) α ∈ W)
    (x : K) (α : σ →₀ ℕ) :
    coefficients (basisPolynomialLift b S x - monomial 0 (I x)) α ∈ W := by
  let D : K →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
    basisPolynomialLift b S - (realMonomial 0).comp I
  have hD : ∀ k β, coefficients (D (b k)) β ∈ W := by
    intro k β
    simp only [D, LinearMap.sub_apply, LinearMap.comp_apply, realMonomial_apply,
      basisPolynomialLift_basis]
    exact h k β
  have hx := realLinearPolynomial_mem_of_basis b D (fun _ => W) hD x α
  simp only [D, LinearMap.sub_apply, LinearMap.comp_apply, realMonomial_apply] at hx
  exact hx

theorem basisPolynomialLift_shiftedGraded {ι : Type*} (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (w : ι → ℕ) (v : σ → ℕ) (r : ℕ)
    (h : ∀ k, S k ∈ shiftedGradedPolynomialSubmodule e w v r) (x : K) :
    basisPolynomialLift b S x ∈ shiftedGradedPolynomialSubmodule e w v r := by
  intro α
  let W := fun β : σ →₀ ℕ => LinearMap.ker
    (basisGradeProjection e w (Finsupp.weight v β + r) - LinearMap.id)
  have hm := basisPolynomialLift_mem b S W (fun k β => by
    change basisGradeProjection e w (Finsupp.weight v β + r) (coefficients (S k) β) -
      coefficients (S k) β = 0
    exact sub_eq_zero.mpr (h k β)) x α
  exact sub_eq_zero.mp hm

theorem basisPolynomialLift_coefficientBound {ι : Type*} (b : Basis κ ℝ K)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (T : σ → ℝ) (M : ℝ)
    (h : ∀ k, CoefficientBound e T M (S k)) (x : K) :
    CoefficientBound e T ((Fintype.card κ : ℝ) * M * ‖b.equivFun x‖)
      (basisPolynomialLift b S x) := by
  classical
  intro α i
  rw [basisPolynomialLift_coefficients]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  calc
    |∑ k, b.equivFun x k * e.repr (coefficients (S k) α) i| ≤
        ∑ k, |b.equivFun x k * e.repr (coefficients (S k) α) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : κ, ‖b.equivFun x‖ * (M / monomialScale T α) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm (b.equivFun x) k) (h k α i)
        (abs_nonneg _) (norm_nonneg _)
    _ = ((Fintype.card κ : ℝ) * M * ‖b.equivFun x‖) / monomialScale T α := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem basisPolynomialLift_coefficientGrid {ι : Type*} (b : Basis κ ℝ K)
    (R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (e : Basis ι ℝ (ℝ ⊗[ℚ] L))
    (l m : ℕ) (hR : ∀ k, CoefficientGrid e m (R k))
    (x : K) (hx : b.equivFun x ∈ realDenominatorGrid l) :
    CoefficientGrid e (m * l) (basisPolynomialLift b R x) := by
  intro α
  have h := realDenominatorGrid_linear_combination l m (b.equivFun x)
    (fun k i => e.repr (coefficients (R k) α) i) hx (fun k => hR k α)
  convert h using 1
  ext i
  rw [basisPolynomialLift_coefficients]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply,
    Finset.sum_apply, Pi.smul_apply]

end VectorPolynomial

namespace NilpotentLieBCHGroup

variable {σ κ K L : Type*} [Fintype κ] [AddCommGroup K] [Module ℝ K]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥}

theorem PolynomialLiftSystemMod.extend_basis (b : Basis κ ℝ K)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L)) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (h : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R) :
    PolynomialLiftSystemMod (V.restrictScalars ℚ) P
      (basisPolynomialLift b S) (basisPolynomialLift b R) := by
  let D := basisPolynomialLift b S -
    (dualAdjointRealLinearEquiv P).toLinearMap.comp (basisPolynomialLift b R)
  intro x α
  apply realLinearPolynomial_mem_of_basis b D (fun _ => V) _ x α
  intro k β
  change coefficients (basisPolynomialLift b S (b k) -
    dualAdjoint P (basisPolynomialLift b R (b k))) β ∈ V
  rw [basisPolynomialLift_basis, basisPolynomialLift_basis]
  exact h k β

omit [Fintype κ] in
theorem basisPolynomialLift_adjoint (b : Basis κ ℝ K) (A : PolynomialGroup σ hnil)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    basisPolynomialLift b (fun k => dualAdjoint A (S k)) =
      (dualAdjointRealLinearEquiv A).toLinearMap.comp (basisPolynomialLift b S) := by
  apply b.ext
  intro k
  simp only [basisPolynomialLift_basis, LinearMap.comp_apply,
    LinearEquiv.coe_coe, dualAdjointRealLinearEquiv_apply]

theorem basisPolynomialLift_adjoint_residual (b : Basis κ ℝ K)
    (A : PolynomialGroup σ hnil) (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (I : K →ₗ[ℝ] ℝ ⊗[ℚ] L) (W : Submodule ℝ (ℝ ⊗[ℚ] L))
    (h : ∀ k α, coefficients (dualAdjoint A (S k) - monomial 0 (I (b k))) α ∈ W)
    (x : K) (α : σ →₀ ℕ) :
    coefficients (dualAdjoint A (basisPolynomialLift b S x) - monomial 0 (I x)) α ∈ W := by
  have hx := basisPolynomialLift_residual b (fun k => dualAdjoint A (S k)) I W h x α
  rw [basisPolynomialLift_adjoint] at hx
  exact hx

end NilpotentLieBCHGroup

theorem real_bracket_mem_of_basis {κ K L : Type*} [Fintype κ]
    [AddCommGroup K] [Module ℝ K] [LieRing L] [LieAlgebra ℝ L]
    (b : Basis κ ℝ K) (I : K →ₗ[ℝ] L) (W : Submodule ℝ L) (p : L)
    (h : ∀ k, ⁅p, I (b k)⁆ ∈ W) (x : K) : ⁅p, I x⁆ ∈ W := by
  classical
  rw [← b.sum_repr x, map_sum, lie_sum]
  apply W.sum_mem
  intro k _
  rw [map_smul, lie_smul]
  exact W.smul_mem _ (h k)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype κ] {s : ℕ}

structure FormalInductionState (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L)
    (w : μ → ℕ) (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (e : Basis κ ℚ K) (T : σ → ℝ) (j : ℕ) (p : ℝ) where
  P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot
  S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  small : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)
  k : σ → κ → ℝ
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p
  constant_zero : coefficients P.coord 0 = 0
  mem_U : ∀ α, coefficients P.coord α ∈ U
  graded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
  horizontal : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K.baseChange ℝ
  lower_log : ∀ α d, 2 ≤ d → d < j →
    basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ
  lower_bracket : ∀ d < j - 1, ∀ z α,
    ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α), (1 : ℝ) ⊗ₜ[ℚ] (e z : L)⁆ ∈ V.baseChange ℝ
  lift_system : PolynomialLiftSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P S R
  derivative_system : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational
    (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S (k i))
  S_shift : ∀ z, S z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  R_shift : ∀ z, R z ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  small_shift : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  rational_shift : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1
  S_remainder : ∀ z α, coefficients (S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
    V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  R_remainder : ∀ z α, coefficients (R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
    V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  small_remainder : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  rational_remainder : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule
  S_bound : ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (S z)
  R_grid : ∀ z, CoefficientGrid (b.baseChange ℝ) denominator (R z)
  small_bound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i) (small i)
  rational_grid : ∀ i, CoefficientGrid (b.baseChange ℝ) denominator (rational i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}

def FormalCorrectionProperty (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L)
    (w : μ → ℕ) (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (g : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) : Prop :=
  (∀ α, coefficients g.coord α ∈ U) ∧
    g.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
    coefficients g.coord 0 = 0

structure FormalInductionRun (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L)
    (w : μ → ℕ) (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (eK : Basis κ ℚ K) (T : σ → ℝ)
    (original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot) (r : ℕ) (q : ℝ) where
  state : F.FormalInductionState b w U V K eK T (2 + r) q
  left : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
  right : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp ((r + 1 : ℝ) * q)
  state_denominator_dvd : state.denominator ∣ denominator
  left_length : left.length = 2 * r
  right_length : right.length = 2 * r
  left_good : ∀ g ∈ left, F.FormalCorrectionProperty b w U g
  right_good : ∀ g ∈ right, F.FormalCorrectionProperty b w U g
  left_bound : ∀ g ∈ left, CoefficientBound (b.baseChange ℝ) T (Real.exp q) g.coord
  right_grid : ∀ g ∈ right, CoefficientGrid (b.baseChange ℝ) denominator g.coord
  factorization : left.prod * state.P * right.prod = original

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s j : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ} {p q : ℝ}

noncomputable def FormalInductionState.enlarge
    (X : F.FormalInductionState b w U V K eK T j p) (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.FormalInductionState b w U V K eK T j q :=
  { X with
    denominator_bound := X.denominator_bound.trans (Real.exp_le_exp.mpr hpq)
    S_bound := fun z => (X.S_bound z).mono _ T hT (Real.exp_le_exp.mpr hpq)
    small_bound := fun i => (X.small_bound i).mono _ T hT
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpq) (hT i).le) }

@[simp] theorem FormalInductionState.enlarge_P
    (X : F.FormalInductionState b w U V K eK T j p) (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    (X.enlarge hpq hT).P = X.P := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]

structure FormalStageGeometry (b : Basis μ ℚ L) (w : μ → ℕ)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V)) (j H : ℕ) where
  bracketSpace : Submodule ℚ L
  currentSpace : Submodule ℚ L
  bracketRank : ℕ
  currentRank : ℕ
  bracketBasis : Basis (Fin bracketRank) ℚ bracketSpace
  currentBasis : Basis (Fin currentRank) ℚ currentSpace
  bracket_grade : ∀ x ∈ bracketSpace.baseChange ℝ,
    basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x
  bracket_U : bracketSpace.baseChange ℝ ≤ U.toSubmodule
  bracket_K : j = 2 → bracketSpace.baseChange ℝ ≤ K.baseChange ℝ
  bracket_V : 2 < j → bracketSpace.baseChange ℝ ≤ V.baseChange ℝ
  bracket_complete : ∀ x ∈ U,
    basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x →
    (j = 2 → x ∈ K.baseChange ℝ) → (2 < j → x ∈ V.baseChange ℝ) →
    x ∈ bracketSpace.baseChange ℝ
  current_grade : ∀ x ∈ currentSpace.baseChange ℝ,
    basisGradeProjection (b.baseChange ℝ) w j x = x
  current_U : currentSpace.baseChange ℝ ≤ U.toSubmodule
  current_projection : ∀ x ∈ U, basisGradeProjection (b.baseChange ℝ) w j x ∈ currentSpace.baseChange ℝ
  bracket_matrix_height : ∀ i z,
    RationalHeightLE (bracketSystemMatrix bracketBasis f (fun z => (eK z : L)) i z) H
  current_matrix_height : ∀ i z, RationalHeightLE (subspaceQuotientMatrix currentBasis f i z) H
  bracket_basis_height : ∀ i z, RationalHeightLE (b.repr (bracketBasis z : L) i) H
  current_basis_height : ∀ i z, RationalHeightLE (b.repr (currentBasis z : L) i) H

theorem FormalInductionState.bracket_source {s j H : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
    {eK : Basis κ ℚ K} {f : Basis ι ℚ (L ⧸ V)} {T : σ → ℝ} {p : ℝ}
    (X : F.FormalInductionState b w U V K eK T j p)
    (G : FormalStageGeometry b w U V K eK f j H)
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule) (hj : 2 ≤ j) :
    ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients X.P.coord α) ∈
      G.bracketSpace.baseChange ℝ := by
  intro α
  apply G.bracket_complete _ (hU _ _ (X.mem_U α))
  · exact basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j - 1} _
  · intro hj2
    subst j
    exact X.horizontal α
  · intro hj2
    exact X.lower_log α (j - 1) (by omega) (by omega)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ}

noncomputable def FormalInductionRun.start {p : ℝ}
    (X : F.FormalInductionState b w U V K eK T 2 p) :
    F.FormalInductionRun b w U V K eK T X.P 0 p where
  state := X
  left := []
  right := []
  denominator := X.denominator
  denominator_pos := X.denominator_pos
  denominator_bound := by simpa using X.denominator_bound
  state_denominator_dvd := dvd_refl _
  left_length := by simp
  right_length := by simp
  left_good := by simp
  right_good := by simp
  left_bound := by simp
  right_grid := by simp
  factorization := by simp

noncomputable def FormalInductionRun.extend
    {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot} {r : ℕ} {q q' : ℝ}
    (W : F.FormalInductionRun b w U V K eK T original r q)
    (hq : q ≤ q') (hT : ∀ i, 0 < T i)
    (Y : F.FormalInductionState b w U V K eK T (2 + (r + 1)) q')
    (A₁ A₂ B₁ B₂ : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hfactor : (A₁ * A₂) * Y.P * (B₂ * B₁) = W.state.P)
    (hA₁ : F.FormalCorrectionProperty b w U A₁)
    (hA₂ : F.FormalCorrectionProperty b w U A₂)
    (hB₁ : F.FormalCorrectionProperty b w U B₁)
    (hB₂ : F.FormalCorrectionProperty b w U B₂)
    (hA₁bound : CoefficientBound (b.baseChange ℝ) T (Real.exp q') A₁.coord)
    (hA₂bound : CoefficientBound (b.baseChange ℝ) T (Real.exp q') A₂.coord)
    (hB₁grid : CoefficientGrid (b.baseChange ℝ) Y.denominator B₁.coord)
    (hB₂grid : CoefficientGrid (b.baseChange ℝ) Y.denominator B₂.coord) :
    F.FormalInductionRun b w U V K eK T original (r + 1) q' := by
  refine {
    state := Y
    left := W.left ++ [A₁, A₂]
    right := [B₂, B₁] ++ W.right
    denominator := W.denominator * Y.denominator
    denominator_pos := Nat.mul_pos W.denominator_pos Y.denominator_pos
    denominator_bound := ?_
    state_denominator_dvd := dvd_mul_left _ _
    left_length := ?_
    right_length := ?_
    left_good := ?_
    right_good := ?_
    left_bound := ?_
    right_grid := ?_
    factorization := ?_ }
  · have hmul : (r + 1 : ℝ) * q ≤ (r + 1 : ℝ) * q' :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    calc
      ((W.denominator * Y.denominator : ℕ) : ℝ) =
          (W.denominator : ℝ) * (Y.denominator : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp ((r + 1 : ℝ) * q') * Real.exp q' :=
        mul_le_mul (W.denominator_bound.trans (Real.exp_le_exp.mpr hmul))
          Y.denominator_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp ((r + 1 + 1 : ℝ) * q') := by rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp (((r + 1 : ℕ) + 1 : ℝ) * q') := by push_cast; rfl
  · simp only [List.length_append, List.length_cons, List.length_nil, W.left_length]
    omega
  · simp only [List.length_append, List.length_cons, List.length_nil, W.right_length]
    omega
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact W.left_good g hg
    · exact hA₁
    · exact hA₂
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl) | hg
    · exact hB₂
    · exact hB₁
    · exact W.right_good g hg
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact (W.left_bound g hg).mono _ T hT (Real.exp_le_exp.mpr hq)
    · exact hA₁bound
    · exact hA₂bound
  · intro g hg α
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (rfl | rfl) | hg
    · exact realDenominatorGrid_subset_of_dvd Y.denominator_pos
        (dvd_mul_left _ _) (hB₂grid α)
    · exact realDenominatorGrid_subset_of_dvd Y.denominator_pos
        (dvd_mul_left _ _) (hB₁grid α)
    · exact realDenominatorGrid_subset_of_dvd W.denominator_pos
        (dvd_mul_right _ _) (W.right_grid g hg α)
  · have h : W.left.prod * ((A₁ * A₂) * Y.P * (B₂ * B₁)) * W.right.prod = original := by
      rw [hfactor]
      exact W.factorization
    simpa only [List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem FormalCorrectionProperty.mul
    {L μ σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} (hgraded : BasisHomogeneousBrackets b w)
    {A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}
    (hA : F.FormalCorrectionProperty b w U A) (hB : F.FormalCorrectionProperty b w U B) :
    F.FormalCorrectionProperty b w U (A * B) := by
  refine ⟨?_, ?_, ?_⟩
  · let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
      { U.toSubmodule.restrictScalars ℚ with lie_mem' := U.lie_mem }
    exact lieBCH_mem (coefficientLieSubalgebra Uq) s hA.1 hB.1
  · exact lieBCH_mem
      (gradedPolynomialSubalgebra (b.baseChange ℝ) w (hgraded.baseChange b w) (fun _ : σ => 1))
      s hA.2.1 hB.2.1
  · have h := eval_lieBCH (fun _ : σ => (0 : ℚ)) s A.coord B.coord
    simp only [eval_zero_eq_coefficient, hA.2.2, hB.2.2] at h
    change coefficients (lieBCH s A.coord B.coord) 0 = 0
    rw [h]
    change ((1 : F.realification.Group) * 1).coord = 0
    rw [one_mul]
    rfl

theorem FormalCorrectionProperty.list_prod
    {L μ σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} (hgraded : BasisHomogeneousBrackets b w)
    (rs : List (PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot))
    (hrs : ∀ r ∈ rs, F.FormalCorrectionProperty b w U r) :
    F.FormalCorrectionProperty b w U rs.prod := by
  induction rs with
  | nil =>
    refine ⟨?_, (gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)).zero_mem, ?_⟩
    · intro α
      change coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈ U
      simp only [map_zero, Finsupp.zero_apply, zero_mem]
    · change coefficients (0 : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0
      simp only [map_zero, Finsupp.zero_apply]
  | cons r rs ih =>
    exact (hrs r List.mem_cons_self).mul hgraded (ih (fun x hx => hrs x (List.mem_cons_of_mem r hx)))

theorem exists_formal_induction_run_product_controls (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w)
    {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L} {eK : Basis κ ℚ K}
    {T : σ → ℝ} (_hT : ∀ i, 0 < T i)
    {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}
    {r : ℕ} (_hr : r ≤ s) {q : ℝ}
    (W : F.FormalInductionRun b w U V K eK T original r q)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hStructure : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    {p : ℝ} (_hp : 0 ≤ p) (_hqp : q ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hDenom : (W.denominator : ℝ) ≤ Real.exp p),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ W.denominator ∣ m ∧
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) W.left.prod.coord ∧
      CoefficientGrid (b.baseChange ℝ) m W.right.prod.coord ∧
      F.FormalCorrectionProperty b w U W.left.prod ∧
      F.FormalCorrectionProperty b w U W.right.prod := by
  obtain ⟨A, hA, hslow⟩ := exists_formal_polynomial_product_bound s 1 (2 * s)
  obtain ⟨B, hB, hgrid⟩ := exists_formal_polynomial_product_grid s (2 * s)
  let C := max A B
  refine ⟨C, hA.trans (Nat.le_max_left A B), ?_⟩
  intro L μ κ σ _ _ _ _ _ F b w hF hgraded U V K eK T hT original r hr q W H hH hStructure
    p hp hqp hμ hσ hHp hDenom
  have hAC : (p + A) ^ A ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_left A B)
  have hBC : (p + B) ^ B ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_right A B)
  have hleft : CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + A) ^ A)) W.left.prod.coord := by
    apply hslow F b w hF H p hH hp hμ hσ hHp hStructure T hT W.left
    · rw [W.left_length]
      exact Nat.mul_le_mul_left 2 hr
    · intro x hx
      exact F.gradedPolynomial_mem_adapted b w hF (fun _ => 1) x.coord (W.left_good x hx).2.1
    · intro x hx
      apply (W.left_bound x hx).mono _ T hT (Real.exp_le_exp.mpr ?_)
      simpa only [pow_one] using hqp.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2))
  obtain ⟨m, hm, hmp, hdm, hproducts⟩ :=
    hgrid F b w hF H p hH hp hμ hσ hHp hStructure W.denominator W.denominator_pos hDenom
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hBC), hdm,
    hleft.mono _ T hT (Real.exp_le_exp.mpr hAC), ?_,
    FormalCorrectionProperty.list_prod hgraded W.left W.left_good,
    FormalCorrectionProperty.list_prod hgraded W.right W.right_good⟩
  apply hproducts W.right
  · rw [W.right_length]
    exact Nat.mul_le_mul_left 2 hr
  · intro x hx
    exact F.gradedPolynomial_mem_adapted b w hF (fun _ => 1) x.coord (W.right_good x hx).2.1
  · exact W.right_grid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis μ ℚ L} {w : μ → ℕ}
  {U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)} {V K : Submodule ℚ L}
  {eK : Basis κ ℚ K} {T : σ → ℝ} {q : ℝ}
  {original : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot}

theorem FormalInductionRun.terminal_lower_log
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (α : σ →₀ ℕ) (d : ℕ) (hd : 2 ≤ d) (hds : d ≤ s) :
    basisGradeProjection (b.baseChange ℝ) w d (coefficients W.state.P.coord α) ∈ V.baseChange ℝ :=
  W.state.lower_log α d hd (by omega)

theorem FormalInductionRun.terminal_lower_bracket
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q)
    (hs : 2 ≤ s) (d : ℕ) (hd : d < s) (z : κ) (α : σ →₀ ℕ) :
    ⁅basisGradeProjection (b.baseChange ℝ) w d (coefficients W.state.P.coord α),
      (1 : ℝ) ⊗ₜ[ℚ] (eK z : L)⁆ ∈ V.baseChange ℝ :=
  W.state.lower_bracket d (by omega) z α

theorem FormalInductionRun.terminal_remainders
    (W : F.FormalInductionRun b w U V K eK T original (s - 1) q) (hs : 2 ≤ s) :
    (∀ z α, coefficients (W.state.S z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (eK z : L))) α ∈ V.baseChange ℝ) ∧
    (∀ z α, coefficients (W.state.R z - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (eK z : L))) α ∈ V.baseChange ℝ) ∧
    (∀ i α, coefficients (W.state.small i) α ∈ V.baseChange ℝ) ∧
    (∀ i α, coefficients (W.state.rational i) α ∈ V.baseChange ℝ) := by
  have hindex : 2 + (s - 1) = s + 1 := by omega
  have hspace : V.baseChange ℝ ⊔ (F.realLayer (2 + (s - 1))).toSubmodule = V.baseChange ℝ := by
    rw [hindex, F.realLayer_terminal]
    exact sup_bot_eq _
  exact ⟨fun z α => hspace ▸ W.state.S_remainder z α,
    fun z α => hspace ▸ W.state.R_remainder z α,
    fun i α => hspace ▸ W.state.small_remainder i α,
    fun i α => hspace ▸ W.state.rational_remainder i α⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
