/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use MvPolynomial coefficient lemmas explicitly for the older coefficient API.
All upstream theorem statements are unchanged. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.HomogeneousQuotientSymbolLiftBounds
import OAI.Combinatorics.Progressions.Nilpotent.RealFunctionalBCH
import OAI.Combinatorics.Progressions.Sampling.ScalarFunctionalCoefficientGrid

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem realifyFunctional_eq_sum_basis {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional θ x = ∑ i, (b.baseChange ℝ).repr x i * (θ (b i) : ℝ) := by
  classical
  calc
    realifyFunctional θ x = realifyFunctional θ
        (∑ i, (b.baseChange ℝ).repr x i • (b.baseChange ℝ) i) :=
      congrArg (realifyFunctional θ) ((b.baseChange ℝ).sum_repr x).symm
    _ = _ := by
      simp only [map_sum, map_smul, Basis.baseChange_apply, realifyFunctional_tmul,
        one_mul, smul_eq_mul]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def scalarSymbolPolynomial (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (g : F.RealPolynomialSymbolGroup w) : MvPolynomial σ ℝ :=
  coordinate (realifyFunctional θ).toAddMonoidHom
    (F.realGradedSymbolPolynomial b ω hF w g.coord)

@[simp] theorem coeff_scalarSymbolPolynomial (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (g : F.RealPolynomialSymbolGroup w) (α : σ →₀ ℕ) :
    (F.scalarSymbolPolynomial b ω hF w θ g).coeff α =
      realifyFunctional θ
        (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) := by
  simp only [scalarSymbolPolynomial, coeff_coordinate, LinearMap.toAddMonoidHom_coe]

theorem realGradedSymbolPolynomial_slow_coordinates (T : σ → ℝ)
    (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) (i : ι) :
    |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i| ≤
      M / monomialScale T α := by
  by_cases h : Finsupp.weight w α = ω i
  · have hc := F.realGradedSymbolPolynomial_coordinate b ω hF w g.coord ⟨(α, i), h⟩
    exact (congrArg abs hc).le.trans (hg ⟨(α, i), h⟩)
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord α i h, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem scalarSymbolPolynomial_slow_coefficients [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M H : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hθ : ∀ i, |(θ (F.associatedGradedBasis b ω hF i) : ℝ)| ≤ H)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) :
    |(F.scalarSymbolPolynomial b ω hF w θ g).coeff α| ≤
      (Fintype.card ι : ℝ) * H * M / monomialScale T α := by
  classical
  rw [F.coeff_scalarSymbolPolynomial, realifyFunctional_eq_sum_basis (F.associatedGradedBasis b ω hF)]
  calc
    _ ≤ ∑ i, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i *
          (θ (F.associatedGradedBasis b ω hF i) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (M / monomialScale T α) * H := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hθ i) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right
          (F.realGradedSymbolPolynomial_slow_coordinates b ω hF w T hT hM g hg α i) hH)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem realGradedSymbolPolynomial_rational_coordinates [Fintype ι] (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g)
    (α : σ →₀ ℕ) :
    ((F.associatedGradedBasis b ω hF).baseChange ℝ).equivFun
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α)
        ∈ realDenominatorGrid m := by
  classical
  obtain ⟨a, ha⟩ := hg
  refine ⟨fun i => if h : Finsupp.weight w α = ω i then a ⟨(α, i), h⟩ else 0, ?_⟩
  funext i
  change ((if h : Finsupp.weight w α = ω i then a ⟨(α, i), h⟩ else 0 : ℤ) : ℝ) =
    (m : ℝ) * ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
      (coefficients (F.realGradedSymbolPolynomial b ω hF w g.coord) α) i
  by_cases h : Finsupp.weight w α = ω i
  · rw [dite_eq_left h, F.realGradedSymbolPolynomial_coordinate b ω hF w g.coord ⟨(α, i), h⟩]
    exact congrFun ha ⟨(α, i), h⟩
  · rw [dite_eq_right h, Int.cast_zero,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w g.coord α i h, mul_zero]

theorem scalarSymbolPolynomial_rational_coefficients [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (m : ℕ)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w m g) :
    realPolynomialCoefficientGrid
      (matrixDenominator (fun (_ : Unit) i => θ (F.associatedGradedBasis b ω hF i)) * m)
      (F.scalarSymbolPolynomial b ω hF w θ g) := by
  classical
  have h : ∀ α, ∃ z : ℤ,
      ((matrixDenominator (fun (_ : Unit) i => θ (F.associatedGradedBasis b ω hF i)) * m : ℕ) : ℝ) *
        (F.scalarSymbolPolynomial b ω hF w θ g).coeff α = (z : ℝ) := by
    intro α
    rw [F.coeff_scalarSymbolPolynomial]
    exact realifyFunctional_denominator_grid (F.associatedGradedBasis b ω hF) θ m _
      (F.realGradedSymbolPolynomial_rational_coordinates b ω hF w m g hg α)
  choose z hz using h
  exact ⟨z, funext (fun α => (hz α).symm)⟩

theorem scalarSymbolPolynomial_slow_coefficients_of_height [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M) {H : ℕ}
    (hθ : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolSlowBound b ω hF w T M g)
    (α : σ →₀ ℕ) :
    |(F.scalarSymbolPolynomial b ω hF w θ g).coeff α| ≤
      (Fintype.card ι : ℝ) * H * M / monomialScale T α :=
  F.scalarSymbolPolynomial_slow_coefficients b ω hF w θ T hT hM (Nat.cast_nonneg H)
    (fun i => (hθ i).abs_real_le) g hg α

theorem scalarSymbolPolynomial_exists_coefficient_grid [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) {H : ℕ}
    (hθ : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (m : ℕ) (hm : 0 < m) (g : F.RealPolynomialSymbolGroup w)
    (hg : F.SymbolRationalGrid b ω hF w m g) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ Fintype.card ι * m ∧
      realPolynomialCoefficientGrid q (F.scalarSymbolPolynomial b ω hF w θ g) := by
  refine ⟨_, Nat.mul_pos (scalarFunctionalDenominator_pos (F.associatedGradedBasis b ω hF) θ) hm,
    Nat.mul_le_mul_right m (scalarFunctionalDenominator_le (F.associatedGradedBasis b ω hF) θ hθ), ?_⟩
  exact F.scalarSymbolPolynomial_rational_coefficients b ω hF w θ m g hg

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem scalarSymbolPolynomial_mul (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (hθ : ∀ x y : F.AssociatedGraded, θ ⁅x, y⁆ = 0) (hs : 1 ≤ s)
    (x y : F.RealPolynomialSymbolGroup w) :
    F.scalarSymbolPolynomial b ω hF w θ (x * y) =
      F.scalarSymbolPolynomial b ω hF w θ x + F.scalarSymbolPolynomial b ω hF w θ y := by
  apply MvPolynomial.funext
  intro u
  simp only [scalarSymbolPolynomial, MvPolynomial.eval_add, ← coordinate_eval₂,
    NilpotentLieBCHGroup.coord_mul, map_lieBCH]
  have he := map_lieBCH (eval₂Lie (R := ℚ) (S := ℝ) u) s
    (F.realGradedSymbolPolynomial b ω hF w x.coord)
    (F.realGradedSymbolPolynomial b ω hF w y.coord)
  rw [eval₂Lie_apply] at he
  rw [he]
  exact realifyFunctional_lieBCH θ hθ hs _ _

theorem scalarSymbolPolynomial_eq_zero_of_fast
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hθ : ∀ x ∈ W, θ x = 0) (P : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    F.scalarSymbolPolynomial b ω hF w θ P = 0 := by
  have hle : W.toSubmodule ≤ LinearMap.ker θ := hθ
  ext α
  rw [F.coeff_scalarSymbolPolynomial, MvPolynomial.coeff_zero]
  apply (mem_realified_frequency_kernel_iff θ _).mp
  apply Submodule.baseChange_mono ℝ hle
  exact (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w W P.coord).mp hP α

theorem scalarSymbolPolynomial_approximation_of_factorization [Fintype ι]
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (hθlie : ∀ x y : F.AssociatedGraded, θ ⁅x, y⁆ = 0) (hs : 1 ≤ s)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (R M : ℝ) (hM : 0 ≤ M)
    {H m : ℕ} (hm : 0 < m)
    (hθH : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (hden : ((H ^ Fintype.card ι * m : ℕ) : ℝ) ≤ R)
    (hslow : (Fintype.card ι : ℝ) * H * M ≤ R)
    (E P Q X : F.RealPolynomialSymbolGroup w) (hprod : E * P * Q = X)
    (hE : F.SymbolSlowBound b ω hF w T M E)
    (hQ : F.SymbolRationalGrid b ω hF w m Q)
    (W : LieSubalgebra ℚ F.AssociatedGraded) (hθW : ∀ x ∈ W, θ x = 0)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    PolynomialRationalApproximation T R (F.scalarSymbolPolynomial b ω hF w θ X) := by
  have hsplit : F.scalarSymbolPolynomial b ω hF w θ X =
      F.scalarSymbolPolynomial b ω hF w θ E + F.scalarSymbolPolynomial b ω hF w θ Q := by
    rw [← hprod, F.scalarSymbolPolynomial_mul b ω hF w θ hθlie hs,
      F.scalarSymbolPolynomial_mul b ω hF w θ hθlie hs,
      F.scalarSymbolPolynomial_eq_zero_of_fast b ω hF w θ W hθW P hP, add_zero]
  obtain ⟨q, hq, hqbound, hgrid⟩ :=
    F.scalarSymbolPolynomial_exists_coefficient_grid b ω hF w θ hθH m hm Q hQ
  obtain ⟨Z, hZ⟩ := (realPolynomialCoefficientGrid_iff q _).mp hgrid
  refine ⟨q, hq, (Nat.cast_le.mpr hqbound).trans hden, Z, ?_⟩
  intro α
  have hz := congrArg (fun polynomial => polynomial.coeff α) hZ
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul] at hz
  change ((Z.coeff α : ℤ) : ℝ) = (q : ℝ) * (F.scalarSymbolPolynomial b ω hF w θ Q).coeff α at hz
  rw [hsplit, MvPolynomial.coeff_add, hz,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hq.ne'), add_sub_cancel_right]
  exact (F.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF w θ T hT hM
    hθH E hE α).trans (div_le_div_of_nonneg_right hslow (monomialScale_pos T hT α).le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_quotient_section_residual
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (U : Submodule ℚ V) (S : (V ⧸ U) →ₗ[ℚ] V)
    (hS : ∀ y, U.mkQ (S y) = y)
    (x : ℝ ⊗[ℚ] V) (a c : ℝ ⊗[ℚ] (V ⧸ U))
    (hquot : U.mkQ.baseChange ℝ x = a + c) :
    x - S.baseChange ℝ a - S.baseChange ℝ c ∈ U.baseChange ℝ := by
  have hcomp : U.mkQ.comp S = LinearMap.id := LinearMap.ext hS
  have hSr (y : ℝ ⊗[ℚ] (V ⧸ U)) :
      U.mkQ.baseChange ℝ (S.baseChange ℝ y) = y := by
    have h := congrArg (fun f => LinearMap.baseChange ℝ f) hcomp
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
    exact LinearMap.congr_fun h y
  have hker : U.baseChange ℝ = LinearMap.ker (U.mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using real_baseChange_ker U.mkQ
  rw [hker]
  change U.mkQ.baseChange ℝ (x - S.baseChange ℝ a - S.baseChange ℝ c) = 0
  rw [map_sub, map_sub, hSr, hSr, hquot]
  abel

theorem real_graded_quotient_section_residual
    {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (ω : ι → ℕ) (U : Submodule ℚ V)
    (hU : BasisGradedSubmodule b ω U)
    (S : (V ⧸ U) →ₗ[ℚ] V) (hS : ∀ y, U.mkQ (S y) = y)
    (k : ℕ) (x : ℝ ⊗[ℚ] V) (a c : ℝ ⊗[ℚ] (V ⧸ U))
    (hx : basisGradeProjection (b.baseChange ℝ) ω k x = x)
    (hquot : U.mkQ.baseChange ℝ x = a + c) :
    x - basisGradeProjection (b.baseChange ℝ) ω k (S.baseChange ℝ a) -
      basisGradeProjection (b.baseChange ℝ) ω k (S.baseChange ℝ c) ∈ U.baseChange ℝ := by
  have h := hU.baseChange b ω U k _ (real_quotient_section_residual U S hS x a c hquot)
  simpa only [map_sub, hx] using h

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolGradeEvaluation_quotientLift
    {Q : Type*} [AddCommGroup Q] [Module ℚ Q] [Module ℝ Q] [IsScalarTower ℚ ℝ Q]
    (k : ℕ) (S : Q →ₗ[ℝ] (ℝ ⊗[ℚ] F.AssociatedGraded))
    (p : VectorPolynomial σ ℚ Q)
    (hp : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0) (t : σ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF w k t
      (F.homogeneousQuotientSymbolLift b ω hF w k S p) =
        basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
          (S (eval₂ t p)) := by
  rw [F.realSymbolGradeEvaluation_apply, F.homogeneousQuotientSymbolLift_pure]
  exact F.homogeneousQuotientSymbolLift_eval b ω hF w k S p hp t

theorem restricted_symbol_grade_terminal
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realGradedSymbolPolynomial b ω hF w x) ∈ U.baseChange ℝ ↔
      ∀ j ≤ s, F.realSymbolGradeEvaluation b ω hF w j t x ∈ U.baseChange ℝ := by
  constructor
  · intro hx j _
    rw [F.realSymbolGradeEvaluation_eq_projection]
    exact hU.baseChange (F.associatedGradedBasis b ω hF) ω U j _ hx
  · intro hx
    let y := eval₂ t (F.realGradedSymbolPolynomial b ω hF w x)
    have hfull : basisBelowProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ)
        ω (s + 1) y = y := by
      apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
      ext i
      rw [basisBelowProjection_repr, ite_eq_left (Nat.lt_succ_of_le
        (F.adaptedBasis_weight_le_step b ω hF i))]
    change y ∈ U.baseChange ℝ
    rw [← hfull, basisBelowProjection_eq_sum_grades]
    apply Submodule.sum_mem
    intro j hj
    have h := hx j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    rwa [F.realSymbolGradeEvaluation_eq_projection] at h

theorem restricted_symbol_grade_matching
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
    (hS : ∀ y, U.mkQ (S y) = y)
    (k : ℕ) (Z E R : F.RealPolynomialSymbolGroup w)
    (K₀ K : Set (σ → ℝ)) (hK : K ⊆ K₀)
    (pS pR : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (hpS : ∀ α, Finsupp.weight w α ≠ k → coefficients pS α = 0)
    (hpR : ∀ α, Finsupp.weight w α ≠ k → coefficients pR α = 0)
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈ U.baseChange ℝ)
    (hquot : ∀ t ∈ K,
      U.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF w k t (E⁻¹ * Z * R⁻¹).coord) =
          eval₂ t pS + eval₂ t pR) :
    ∃ A D : F.RealPolynomialSymbolGroup w,
      A.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pS ∧
      D.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pR ∧
      A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      (E * A) * ((E * A)⁻¹ * Z * (D * R)⁻¹) * (D * R) = Z ∧
      (∀ t, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord =
          F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord) ∧
      ∀ t ∈ K, ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord ∈
          U.baseChange ℝ := by
  let A : F.RealPolynomialSymbolGroup w :=
    ⟨F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pS⟩
  let D : F.RealPolynomialSymbolGroup w :=
    ⟨F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) pR⟩
  have hlift (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
      F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ) p ∈
        (F.polynomialSymbolFiltration w).realification.layer k := by
    rw [← F.homogeneousQuotientSymbolLift_pure b ω hF w k (S.baseChange ℝ) p]
    exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer
      (F.polynomialSymbolBasis b ω hF w) (fun z => ω z.val.2)
      (F.polynomialSymbolFiltration_layer b ω hF w) k _
  have hA : A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k := hlift pS
  have hD : D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k := hlift pR
  have hmiddle : (E * A)⁻¹ * Z * (D * R)⁻¹ = A⁻¹ * (E⁻¹ * Z * R⁻¹) * D⁻¹ := by group
  have hbelow (t : σ → ℝ) (j : ℕ) (hj : j < k) :
      F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord =
        F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord := by
    rw [hmiddle]
    exact F.realSymbolGradeEvaluation_correction_below b ω hF w k t A
      (E⁻¹ * Z * R⁻¹) D hA hD j hj
  refine ⟨A, D, rfl, rfl, hA, hD, by group, hbelow, ?_⟩
  intro t ht j hj
  rcases lt_or_eq_of_le hj with hlt | heq
  · rw [hbelow t j hlt]
    exact hlower t (hK ht) j hlt
  · subst j
    rw [hmiddle, F.realSymbolGradeEvaluation_current_correction b ω hF w k t A
      (E⁻¹ * Z * R⁻¹) D hA hD]
    have hevalA : F.realSymbolGradeEvaluation b ω hF w k t A.coord =
        basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
          (S.baseChange ℝ (eval₂ t pS)) := by
      dsimp only [A]
      apply F.realSymbolGradeEvaluation_quotientLift
      exact hpS
    have hevalD : F.realSymbolGradeEvaluation b ω hF w k t D.coord =
        basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
          (S.baseChange ℝ (eval₂ t pR)) := by
      dsimp only [D]
      apply F.realSymbolGradeEvaluation_quotientLift
      exact hpR
    rw [hevalA, hevalD]
    exact real_graded_quotient_section_residual (F.associatedGradedBasis b ω hF) ω U hU S hS k
      _ (eval₂ t pS) (eval₂ t pR)
      (F.realSymbolGradeEvaluation_homogeneous b ω hF w k t _) (hquot t ht)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

noncomputable def realSymbolGradeQuotientPolynomial
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ) (x : F.RealPolynomialSymbol w) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)) :=
  VectorPolynomial.map ((U.mkQ.baseChange ℝ).restrictScalars ℚ)
    (F.realGradedSymbolPolynomial b ω hF w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
        (fun z => ω z.val.2) k x))

theorem realSymbolGradeQuotientPolynomial_eval
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ)
    (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) =
      U.mkQ.baseChange ℝ (F.realSymbolGradeEvaluation b ω hF w k t x) := by
  exact eval₂_map _ t _

theorem realSymbolGradeQuotientPolynomial_homogeneous
    (U : Submodule ℚ F.AssociatedGraded) (k : ℕ)
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) (hα : Finsupp.weight w α ≠ k) :
    coefficients (F.realSymbolGradeQuotientPolynomial b ω hF w U k x) α = 0 := by
  rw [realSymbolGradeQuotientPolynomial, coefficients_map,
    F.realGradedSymbolPolynomial_gradeProjection_homogeneous b ω hF w k x α hα, map_zero]

theorem restricted_symbol_major_grade_step
    (U : Submodule ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)
    (hS : ∀ y, U.mkQ (S y) = y)
    (k : ℕ) (Z E R : F.RealPolynomialSymbolGroup w)
    (K₀ K : Set (σ → ℝ)) (hK : K ⊆ K₀)
    (hdilate : ∀ t ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * t i) ∈ K)
    (pS pR : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord ∈ U.baseChange ℝ)
    (hquot : ∀ t ∈ K,
      U.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF w k t (E⁻¹ * Z * R⁻¹).coord) =
          eval₂ t pS + eval₂ t pR) :
    ∃ A D : F.RealPolynomialSymbolGroup w,
      A.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
        (weightedHomogeneousPart w k pS) ∧
      D.coord = F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
        (weightedHomogeneousPart w k pR) ∧
      A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
      (E * A) * ((E * A)⁻¹ * Z * (D * R)⁻¹) * (D * R) = Z ∧
      (∀ t, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord =
          F.realSymbolGradeEvaluation b ω hF w j t (E⁻¹ * Z * R⁻¹).coord) ∧
      ∀ t ∈ K, ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF w j t ((E * A)⁻¹ * Z * (D * R)⁻¹).coord ∈
          U.baseChange ℝ := by
  apply F.restricted_symbol_grade_matching b ω hF w U hU S hS k Z E R K₀ K hK
    (weightedHomogeneousPart w k pS) (weightedHomogeneousPart w k pR)
    (weightedHomogeneousPart_homogeneous w k pS)
    (weightedHomogeneousPart_homogeneous w k pR) hlower
  intro t ht
  let p := F.realSymbolGradeQuotientPolynomial b ω hF w U k (E⁻¹ * Z * R⁻¹).coord
  have hp : ∀ α, Finsupp.weight w α ≠ k → coefficients p α = 0 :=
    F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF w U k _
  have heq : ∀ x ∈ K, eval₂ x p = eval₂ x pS + eval₂ x pR := by
    intro x hx
    rw [realSymbolGradeQuotientPolynomial_eval]
    exact hquot x hx
  have h := eval₂_weightedHomogeneousPart_decomposition_on w p pS pR K hdilate k hp heq t ht
  rw [F.realSymbolGradeQuotientPolynomial_eval] at h
  exact h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ)

theorem realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart
    (k : ℕ) (x : F.RealPolynomialSymbol w) :
    F.realGradedSymbolPolynomial b ω hF w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
        (fun z => ω z.val.2) k x) =
      weightedHomogeneousPart w k (F.realGradedSymbolPolynomial b ω hF w x) := by
  apply coefficients.injective
  ext α
  rw [F.realGradedSymbolPolynomial_gradeProjection_coefficient,
    coefficients_weightedHomogeneousPart]
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases hi : ω i = k
  · rw [ite_eq_left hi]
    by_cases hα : Finsupp.weight w α = k
    · rw [ite_eq_left hα]
    · rw [ite_eq_right hα, map_zero, Finsupp.zero_apply]
      exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w x α i
        (by simpa only [hi] using hα)
  · rw [ite_eq_right hi]
    by_cases hα : Finsupp.weight w α = k
    · rw [ite_eq_left hα]
      exact (F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w x α i
        (fun h => hi (h.symm.trans hα))).symm
    · rw [ite_eq_right hα, map_zero, Finsupp.zero_apply]

theorem realGradedSymbolPolynomial_quotient_eq_zero_of_fast
    (W : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W)) :
    VectorPolynomial.map ((W.toSubmodule.mkQ.baseChange ℝ).restrictScalars ℚ)
      (F.realGradedSymbolPolynomial b ω hF w x) = 0 := by
  have hker : W.toSubmodule.baseChange ℝ =
      LinearMap.ker (W.toSubmodule.mkQ.baseChange ℝ) := by
    simpa only [Submodule.ker_mkQ] using real_baseChange_ker W.toSubmodule.mkQ
  apply coefficients.injective
  ext α
  rw [coefficients_map, map_zero, Finsupp.zero_apply]
  have hm := (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w W x).mp hx α
  change coefficients (F.realGradedSymbolPolynomial b ω hF w x) α ∈
    W.toSubmodule.baseChange ℝ at hm
  rw [hker] at hm
  exact hm

theorem realSymbolGradeQuotientPolynomial_normalized_splitting
    (W : LieSubalgebra ℚ F.AssociatedGraded) (k : ℕ)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (hE : F.realSymbolGradeQuotientHom w k E₀ = F.realSymbolGradeQuotientHom w k E)
    (hR : F.realSymbolGradeQuotientHom w k R = F.realSymbolGradeQuotientHom w k R₀) :
    F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k
      (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord =
        F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k (E₀⁻¹ * E).coord +
        F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k (R * R₀⁻¹).coord := by
  have hz : F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k P.coord = 0 := by
    rw [realSymbolGradeQuotientPolynomial,
      F.realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart,
      map_weightedHomogeneousPart,
      F.realGradedSymbolPolynomial_quotient_eq_zero_of_fast b ω hF w W P.coord hP,
      map_zero]
  have hproj := (F.polynomialSymbolFiltration w).realGradeProjection_normalized_splitting
    (F.polynomialSymbolBasis b ω hF w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hF w) k E P R E₀ R₀ hE hR
  have he := congrArg (fun x => VectorPolynomial.map
      ((W.toSubmodule.mkQ.baseChange ℝ).restrictScalars ℚ)
      (F.realGradedSymbolPolynomial b ω hF w x)) hproj
  simp only [map_add] at he
  change F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k
      (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord =
        F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k (E₀⁻¹ * E).coord +
        F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k P.coord +
        F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k (R * R₀⁻¹).coord at he
  simpa only [hz, add_zero] using he

theorem realSymbolGradeQuotientPolynomial_coordinate_normalized_splitting
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (θ : (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule)) →ₗ[ℝ] ℝ) (k : ℕ)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (hE : F.realSymbolGradeQuotientHom w k E₀ = F.realSymbolGradeQuotientHom w k E)
    (hR : F.realSymbolGradeQuotientHom w k R = F.realSymbolGradeQuotientHom w k R₀) :
    coordinate θ.toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k
        (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord) =
      coordinate θ.toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k (E₀⁻¹ * E).coord) +
      coordinate θ.toAddMonoidHom
        (F.realSymbolGradeQuotientPolynomial b ω hF w W.toSubmodule k (R * R₀⁻¹).coord) := by
  rw [F.realSymbolGradeQuotientPolynomial_normalized_splitting b ω hF w W k E P R E₀ R₀ hP hE hR]
  ext α
  simp only [coeff_coordinate, map_add, Finsupp.add_apply, MvPolynomial.coeff_add]

theorem scalarSymbolPolynomial_weightedComponent_normalized_splitting
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (hθ : ∀ x ∈ W, θ x = 0) (k : ℕ)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W))
    (hE : F.realSymbolGradeQuotientHom w k E₀ = F.realSymbolGradeQuotientHom w k E)
    (hR : F.realSymbolGradeQuotientHom w k R = F.realSymbolGradeQuotientHom w k R₀) :
    MvPolynomial.weightedHomogeneousComponent w k
      (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * (E * P * R) * R₀⁻¹)) =
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * E)) +
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (R * R₀⁻¹)) := by
  have hproj := (F.polynomialSymbolFiltration w).realGradeProjection_normalized_splitting
    (F.polynomialSymbolBasis b ω hF w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hF w) k E P R E₀ R₀ hE hR
  have he := congrArg (fun x => F.realGradedSymbolPolynomial b ω hF w x) hproj
  simp only [map_add,
    F.realGradedSymbolPolynomial_gradeProjection_eq_weightedHomogeneousPart] at he
  have hc := congrArg (coordinate (realifyFunctional θ).toAddMonoidHom) he
  have hcoord_add (p q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
      coordinate (realifyFunctional θ).toAddMonoidHom (p + q) =
        coordinate (realifyFunctional θ).toAddMonoidHom p +
        coordinate (realifyFunctional θ).toAddMonoidHom q := by
    ext α
    simp only [coeff_coordinate, map_add, Finsupp.add_apply, MvPolynomial.coeff_add]
  simp only [hcoord_add, coordinate_weightedHomogeneousPart] at hc
  change MvPolynomial.weightedHomogeneousComponent w k
      (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * (E * P * R) * R₀⁻¹)) =
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (E₀⁻¹ * E)) +
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ P) +
      MvPolynomial.weightedHomogeneousComponent w k
        (F.scalarSymbolPolynomial b ω hF w θ (R * R₀⁻¹)) at hc
  simpa only [F.scalarSymbolPolynomial_eq_zero_of_fast b ω hF w θ W hθ P hP,
    map_zero, add_zero] using hc

theorem scalarSymbolPolynomial_homogeneous_normalized_splitting
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hθW : ∀ x ∈ W, θ x = 0) (k : ℕ)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : σ => 1) W))
    (hE : F.realSymbolGradeQuotientHom (fun _ : σ => 1) k E₀ =
      F.realSymbolGradeQuotientHom (fun _ : σ => 1) k E)
    (hR : F.realSymbolGradeQuotientHom (fun _ : σ => 1) k R =
      F.realSymbolGradeQuotientHom (fun _ : σ => 1) k R₀) :
    MvPolynomial.homogeneousComponent k
      (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) θ
        (E₀⁻¹ * (E * P * R) * R₀⁻¹)) =
      MvPolynomial.homogeneousComponent k
        (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) θ (E₀⁻¹ * E)) +
      MvPolynomial.homogeneousComponent k
        (F.scalarSymbolPolynomial b ω hF (fun _ : σ => 1) θ (R * R₀⁻¹)) :=
  F.scalarSymbolPolynomial_weightedComponent_normalized_splitting b ω hF
    (fun _ : σ => 1) W θ hθW k E P R E₀ R₀ hP hE hR

end Erdos3.NilpotentLieFiltration

end

end OAI
