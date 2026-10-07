/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)
  (U : Submodule ℚ F.AssociatedGraded)
  (S : (F.AssociatedGraded ⧸ U) →ₗ[ℚ] F.AssociatedGraded)

noncomputable def restrictedMajorCorrection (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    F.RealPolynomialSymbolGroup w :=
  ⟨F.homogeneousQuotientSymbolLift b ω hF w k (S.baseChange ℝ)
    (weightedHomogeneousPart w k p)⟩

noncomputable def restrictedMajorOuterFactors
    (pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U))) :
    ℕ → F.RealPolynomialSymbolGroup w × F.RealPolynomialSymbolGroup w
  | 0 => (1, 1)
  | n + 1 =>
    let previous := restrictedMajorOuterFactors pS pR n
    (previous.1 * F.restrictedMajorCorrection b ω hF w U S (n + 1) (pS n),
      F.restrictedMajorCorrection b ω hF w U S (n + 1) (pR n) * previous.2)

theorem realSymbolGradeEvaluation_zero (x : F.RealPolynomialSymbol w) (t : σ → ℝ) :
    F.realSymbolGradeEvaluation b ω hF w 0 t x = 0 := by
  have hz : basisGradeProjection ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ)
      (fun z => ω z.val.2) 0 x = 0 := by
    apply ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr.injective
    ext z
    rw [basisGradeProjection_repr, ite_eq_right
      (Nat.ne_of_gt (F.adaptedBasis_weight_pos b ω hF z.val.2)), map_zero, Finsupp.zero_apply]
  rw [F.realSymbolGradeEvaluation_apply, hz, map_zero, map_zero]

theorem restricted_major_outerFactors_match
    (hU : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U)
    (hS : ∀ y, U.mkQ (S y) = y)
    (Z : F.RealPolynomialSymbolGroup w)
    (K : ℕ → Set (σ → ℝ)) (hK : ∀ n < s, K (n + 1) ⊆ K n)
    (hdilate : ∀ n < s, ∀ t ∈ K (n + 1), ∀ r : ℚ,
      (fun i => (r : ℝ) ^ w i * t i) ∈ K (n + 1))
    (pS pR : ℕ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ U)))
    (hquot : ∀ n < s, ∀ t ∈ K (n + 1),
      let outer := F.restrictedMajorOuterFactors b ω hF w U S pS pR n
      U.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF w (n + 1) t
          (outer.1⁻¹ * Z * outer.2⁻¹).coord) = eval₂ t (pS n) + eval₂ t (pR n)) :
    let outer := F.restrictedMajorOuterFactors b ω hF w U S pS pR s
    ∀ t ∈ K s,
      eval₂ t (F.realGradedSymbolPolynomial b ω hF w
        (outer.1⁻¹ * Z * outer.2⁻¹).coord) ∈ U.baseChange ℝ := by
  have hind : ∀ n ≤ s, ∀ t ∈ K n, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF w j t
        ((F.restrictedMajorOuterFactors b ω hF w U S pS pR n).1⁻¹ * Z *
          (F.restrictedMajorOuterFactors b ω hF w U S pS pR n).2⁻¹).coord ∈
            U.baseChange ℝ := by
    intro n
    induction n with
    | zero =>
      intro hn t ht j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      rw [F.realSymbolGradeEvaluation_zero]
      exact Submodule.zero_mem _
    | succ n ih =>
      intro hn
      let outer := F.restrictedMajorOuterFactors b ω hF w U S pS pR n
      have hlower : ∀ t ∈ K n, ∀ j < n + 1,
          F.realSymbolGradeEvaluation b ω hF w j t
            (outer.1⁻¹ * Z * outer.2⁻¹).coord ∈ U.baseChange ℝ :=
        fun t ht j hj => ih (by omega) t ht j (by omega)
      obtain ⟨A, D, hA, hD, _, _, _, _, hnext⟩ :=
        F.restricted_symbol_major_grade_step b ω hF w U hU S hS (n + 1)
          Z outer.1 outer.2 (K n) (K (n + 1)) (hK n (by omega))
          (hdilate n (by omega)) (pS n) (pR n) hlower (hquot n (by omega))
      have hAc : A = F.restrictedMajorCorrection b ω hF w U S (n + 1) (pS n) :=
        NilpotentLieBCHGroup.ext hA
      have hDc : D = F.restrictedMajorCorrection b ω hF w U S (n + 1) (pR n) :=
        NilpotentLieBCHGroup.ext hD
      rw [hAc, hDc] at hnext
      exact hnext
  dsimp only
  intro t ht
  apply (F.restricted_symbol_grade_terminal b ω hF w U hU _ t).mpr
  exact hind s le_rfl t ht

end Erdos3.NilpotentLieFiltration

end

end OAI
