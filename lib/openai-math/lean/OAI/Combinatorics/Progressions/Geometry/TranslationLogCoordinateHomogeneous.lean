import OAI.Combinatorics.Progressions.Polynomial.TranslationLogCoordinateWeightedDegree

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped BigOperators

variable {U B : Type*} [Fintype B]

theorem translationLogBasePolynomial_weightedBasis_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous v (weightedBasisGrade w d k)) (i : B) :
    (translationLogBasePolynomial w d (weightedBasis w d hw) f i).IsWeightedHomogeneous
      v (w i) := by
  rw [translationLogBasePolynomial_weightedBasis]
  exact hf (Sum.inl i)

theorem pack_translationLogPhasePolynomial_weightedBasis_isWeightedHomogeneous
    (v : U → ℕ) (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ)
    (hf : ∀ k, (f k).IsWeightedHomogeneous v (weightedBasisGrade w d k)) :
    (packTranslationPolynomial (translationLogPhasePolynomial w d (weightedBasis w d hw) f)).IsWeightedHomogeneous
      (Sum.elim v w) d := by
  classical
  rw [pack_translationLogPhasePolynomial]
  apply (weightedHomogeneousSubmodule ℝ (Sum.elim v w) d).sum_mem
  intro k _
  cases k with
  | inl i =>
    simp only [weightedBasis_inl_polynomial, map_zero, mul_zero]
    exact isWeightedHomogeneous_zero ℝ _ _
  | inr a =>
    simp only [weightedBasis_inr_polynomial, map_monomial, map_one]
    have hleft : (rename Sum.inl (f (Sum.inr a))).IsWeightedHomogeneous (Sum.elim v w)
        (d - Finsupp.weight w a.val) := by
      rw [rename_eq_aeval]
      exact aeval_isWeightedHomogeneous v (Sum.elim v w) _
        (fun i => isWeightedHomogeneous_X ℝ (Sum.elim v w) (Sum.inl i)) (hf (Sum.inr a))
    have hright : (rename Sum.inr (monomial a.val (1 : ℝ))).IsWeightedHomogeneous
        (Sum.elim v w) (Finsupp.weight w a.val) := by
      rw [rename_eq_aeval]
      exact aeval_isWeightedHomogeneous w (Sum.elim v w) _
        (fun i => isWeightedHomogeneous_X ℝ (Sum.elim v w) (Sum.inr i))
        (isWeightedHomogeneous_monomial w a.val 1 rfl)
    simpa only [mem_weightedHomogeneousSubmodule, Nat.sub_add_cancel a.property.le]
      using hleft.mul hright

end Erdos3.PolynomialTranslationLie

end

end OAI
