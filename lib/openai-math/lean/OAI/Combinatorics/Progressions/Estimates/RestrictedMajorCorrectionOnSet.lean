import OAI.Combinatorics.Progressions.Dynamics.RestrictedSymbolGradeIteration

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

attribute [local irreducible] realSymbolGradeEvaluation homogeneousQuotientSymbolLift

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)
  (U : Submodule ℚ F.AssociatedGraded)
  (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

theorem restrictedMajorCorrection_mem_layer (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    (F.restrictedMajorCorrection b ω hF w U S k p).coord ∈
      (F.polynomialSymbolFiltration w).realification.layer k := by
  change F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
    (weightedHomogeneousPart w k p) ∈ _
  rw [← F.homogeneousQuotientSymbolLift_pure b ω hF w k (S.baseChange ℝ)]
  exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer
    (F.polynomialSymbolBasis b ω hF w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hF w) k _

theorem realSymbolGradeEvaluation_restrictedMajorCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) (t : σ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF w k t
      (F.restrictedMajorCorrection b ω hF w U S k p).coord =
    basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω k
      (S.baseChange ℝ (eval₂ t (weightedHomogeneousPart w k p))) := by
  change F.realSymbolGradeEvaluation b ω hF w k t
    (F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
      (weightedHomogeneousPart w k p)) = _
  exact F.realSymbolGradeEvaluation_quotientLift b ω hF w k (S.baseChange ℝ)
    _ (weightedHomogeneousPart_homogeneous w k p) t

theorem restrictedMajorCorrection_residual_grades_congr_on
    (k : ℕ) (Z E R : F.RealPolynomialSymbolGroup w)
    (K : Set (σ → ℝ))
    (hK : ∀ t ∈ K, ∀ r : ℚ, (fun i => (r : ℝ) ^ w i * t i) ∈ K)
    (pS pR qS qR : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (hS : ∀ t ∈ K, eval₂ t pS = eval₂ t qS)
    (hR : ∀ t ∈ K, eval₂ t pR = eval₂ t qR) :
    ∀ t ∈ K, ∀ j ≤ k,
      F.realSymbolGradeEvaluation b ω hF w j t
        ((E * F.restrictedMajorCorrection b ω hF w U S k pS)⁻¹ * Z *
          (F.restrictedMajorCorrection b ω hF w U S k pR * R)⁻¹).coord =
      F.realSymbolGradeEvaluation b ω hF w j t
        ((E * F.restrictedMajorCorrection b ω hF w U S k qS)⁻¹ * Z *
          (F.restrictedMajorCorrection b ω hF w U S k qR * R)⁻¹).coord := by
  intro t ht j hj
  have hmiddle (a d : F.RealPolynomialSymbolGroup w) :
      (E * a)⁻¹ * Z * (d * R)⁻¹ = a⁻¹ * (E⁻¹ * Z * R⁻¹) * d⁻¹ := by group
  rw [hmiddle, hmiddle]
  rcases lt_or_eq_of_le hj with hj | heq
  · rw [F.realSymbolGradeEvaluation_correction_below b ω hF w k t _ _ _
      (F.restrictedMajorCorrection_mem_layer b ω hF w U S k pS)
      (F.restrictedMajorCorrection_mem_layer b ω hF w U S k pR) j hj,
      F.realSymbolGradeEvaluation_correction_below b ω hF w k t _ _ _
      (F.restrictedMajorCorrection_mem_layer b ω hF w U S k qS)
      (F.restrictedMajorCorrection_mem_layer b ω hF w U S k qR) j hj]
  · subst j
    rw [F.realSymbolGradeEvaluation_current_correction b ω hF w k t _ _ _
      (F.restrictedMajorCorrection_mem_layer b ω hF w U S k pS)
      (F.restrictedMajorCorrection_mem_layer b ω hF w U S k pR),
      F.realSymbolGradeEvaluation_current_correction b ω hF w k t _ _ _
      (F.restrictedMajorCorrection_mem_layer b ω hF w U S k qS)
      (F.restrictedMajorCorrection_mem_layer b ω hF w U S k qR)]
    simp only [F.realSymbolGradeEvaluation_restrictedMajorCorrection b ω hF w U S]
    rw [eval₂_weightedHomogeneousPart_eq_on w pS qS K hK hS k t ht,
      eval₂_weightedHomogeneousPart_eq_on w pR qR K hK hR k t ht]

end Erdos3.NilpotentLieFiltration

end

end OAI
