import OAI.Combinatorics.Progressions.Estimates.CurrentLayerPreservation

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realGradedSymbolPolynomial_gradeProjection_coefficient
    (d : ℕ) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x)) α =
      basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
        (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  rw [basisGradeProjection_repr]
  by_cases h : Finsupp.weight w α = ω i
  · rw [F.realGradedSymbolPolynomial_coordinate b ω hlayers w _ ⟨(α, i), h⟩,
      basisGradeProjection_repr,
      F.realGradedSymbolPolynomial_coordinate b ω hlayers w x ⟨(α, i), h⟩]
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w _ α i h,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w x α i h]
    simp

theorem realGradedSymbolPolynomial_gradeProjection
    (d : ℕ) (x : F.RealPolynomialSymbol w) :
    F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x) =
      VectorPolynomial.map
        ((basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ)
          ω d).restrictScalars ℚ)
        (F.realGradedSymbolPolynomial b ω hlayers w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact F.realGradedSymbolPolynomial_gradeProjection_coefficient b ω hlayers w d x α

theorem realGradedSymbolPolynomial_gradeProjection_homogeneous
    (d : ℕ) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ)
    (hα : Finsupp.weight w α ≠ d) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x)) α = 0 := by
  rw [F.realGradedSymbolPolynomial_gradeProjection_coefficient]
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  simp only [basisGradeProjection_repr, map_zero, Finsupp.zero_apply]
  split_ifs with hi
  · exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w x α i
      (fun h => hα (h.trans hi))
  · rfl

theorem realGradedSymbolPolynomial_gradeProjection_map_homogeneous
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (f : (ℝ ⊗[ℚ] F.AssociatedGraded) →ₗ[ℚ] V)
    (d : ℕ) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ)
    (hα : Finsupp.weight w α ≠ d) :
    coefficients (VectorPolynomial.map f
      (F.realGradedSymbolPolynomial b ω hlayers w
        (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) d x))) α = 0 := by
  rw [coefficients_map,
    F.realGradedSymbolPolynomial_gradeProjection_homogeneous b ω hlayers w d x α hα,
    map_zero]

theorem realGradedSymbolPolynomial_eval₂_gradeProjection
    (d : ℕ) (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
      (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
        (fun z => ω z.val.2) d x)) =
      basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
        (eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) := by
  rw [F.realGradedSymbolPolynomial_gradeProjection, eval₂_map]

noncomputable def realSymbolGradeEvaluation (d : ℕ) (t : σ → ℝ) :
    F.RealPolynomialSymbol w →ₗ[ℚ] (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  (eval₂ t).comp ((F.realGradedSymbolPolynomial b ω hlayers w).toLinearMap.comp
    ((basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
      (fun z => ω z.val.2) d).restrictScalars ℚ))

@[simp] theorem realSymbolGradeEvaluation_apply (d : ℕ) (t : σ → ℝ)
    (x : F.RealPolynomialSymbol w) :
    F.realSymbolGradeEvaluation b ω hlayers w d t x =
      eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w
        (basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) d x)) := rfl

theorem realSymbolGradeEvaluation_eq_projection (d : ℕ) (t : σ → ℝ)
    (x : F.RealPolynomialSymbol w) :
    F.realSymbolGradeEvaluation b ω hlayers w d t x =
      basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
        (eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) :=
  F.realGradedSymbolPolynomial_eval₂_gradeProjection b ω hlayers w d x t

theorem realSymbolGradeEvaluation_homogeneous (d : ℕ) (t : σ → ℝ)
    (x : F.RealPolynomialSymbol w) :
    basisGradeProjection ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) ω d
      (F.realSymbolGradeEvaluation b ω hlayers w d t x) =
        F.realSymbolGradeEvaluation b ω hlayers w d t x := by
  simp only [F.realSymbolGradeEvaluation_eq_projection]
  exact basisCoordinateProjection_idempotent
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ) {i | ω i = d} _

theorem realSymbolGradeEvaluation_current_correction (d : ℕ) (t : σ → ℝ)
    (a g c : F.RealPolynomialSymbolGroup w)
    (ha : a.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d)
    (hc : c.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d) :
    F.realSymbolGradeEvaluation b ω hlayers w d t (a⁻¹ * g * c⁻¹).coord =
      F.realSymbolGradeEvaluation b ω hlayers w d t g.coord -
        F.realSymbolGradeEvaluation b ω hlayers w d t a.coord -
        F.realSymbolGradeEvaluation b ω hlayers w d t c.coord := by
  have h := (F.polynomialSymbolFiltration w).real_correction_current_grade
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) d a g c ha hc
  have he := congrArg (fun x => eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) h
  simpa only [realSymbolGradeEvaluation_apply, map_sub] using he

theorem realSymbolGradeEvaluation_correction_below (d : ℕ) (t : σ → ℝ)
    (a g c : F.RealPolynomialSymbolGroup w)
    (ha : a.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d)
    (hc : c.coord ∈ (F.polynomialSymbolFiltration w).realification.layer d)
    (j : ℕ) (hj : j < d) :
    F.realSymbolGradeEvaluation b ω hlayers w j t (a⁻¹ * g * c⁻¹).coord =
      F.realSymbolGradeEvaluation b ω hlayers w j t g.coord := by
  have h := (F.polynomialSymbolFiltration w).real_correction_preserves_grades_below
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) d a g c ha hc j hj
  exact congrArg (fun x => eval₂ t (F.realGradedSymbolPolynomial b ω hlayers w x)) h

end Erdos3.NilpotentLieFiltration

end

end OAI
