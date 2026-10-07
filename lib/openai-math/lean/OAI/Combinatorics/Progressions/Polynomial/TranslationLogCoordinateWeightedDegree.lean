import OAI.Combinatorics.Progressions.Geometry.TranslationLogCoordinateInputBounds

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {U B : Type*}

theorem weightedSupportLE_rename_inl (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial U ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE v n) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) n := by
  rw [rename_eq_aeval]
  exact weightedSupportLE_aeval v (Sum.elim v w) (X ∘ Sum.inl)
    (fun i => weightedSupportLE_X (Sum.elim v w) (Sum.inl i)) hP

theorem weightedSupportLE_rename_inr (v : U → ℕ) (w : B → ℕ)
    {P : MvPolynomial B ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) :
    rename (Sum.inr : B → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) n := by
  rw [rename_eq_aeval]
  exact weightedSupportLE_aeval w (Sum.elim v w) (X ∘ Sum.inr)
    (fun i => weightedSupportLE_X (Sum.elim v w) (Sum.inr i)) hP

namespace PolynomialTranslationLie

variable [Fintype B] (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]

theorem translationLogBasePolynomial_weightedBasis
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ) (i : B) :
    translationLogBasePolynomial w d (weightedBasis w d hw) f i = f (Sum.inl i) := by
  classical
  unfold translationLogBasePolynomial
  rw [Finset.sum_eq_single (Sum.inl i)]
  · simp
  · intro k _ hki
    cases k with
    | inl j =>
      have hji : j ≠ i := fun h => hki (congrArg Sum.inl h)
      simp [Ne.symm hji]
    | inr α => simp
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

theorem translationLogBasePolynomial_weightedSupportLE (v : U → ℕ)
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ)
    (hf : ∀ k, f k ∈ weightedSupportLE v (weightedBasisGrade w d k)) (i : B) :
    translationLogBasePolynomial w d (weightedBasis w d hw) f i ∈ weightedSupportLE v (w i) := by
  rw [translationLogBasePolynomial_weightedBasis]
  exact hf (Sum.inl i)

theorem pack_translationLogPhasePolynomial_weightedSupportLE (v : U → ℕ)
    (f : WeightedBasisIndex w d → MvPolynomial U ℝ)
    (hf : ∀ k, f k ∈ weightedSupportLE v (weightedBasisGrade w d k)) :
    packTranslationPolynomial (translationLogPhasePolynomial w d (weightedBasis w d hw) f) ∈
      weightedSupportLE (Sum.elim v w) d := by
  rw [pack_translationLogPhasePolynomial]
  apply (weightedSupportLE (Sum.elim v w) d).sum_mem
  intro k _
  cases k with
  | inl i =>
    simp only [weightedBasis_inl_polynomial, map_zero, mul_zero]
    exact Submodule.zero_mem _
  | inr α =>
    simp only [weightedBasis_inr_polynomial, map_monomial, map_one]
    have hleft := weightedSupportLE_rename_inl v w (hf (Sum.inr α))
    have hright := weightedSupportLE_rename_inr v w
      (weightedSupportLE_monomial w α.val (1 : ℝ))
    have hh := weightedSupportLE_mul hleft hright
    have hsum : weightedBasisGrade w d (Sum.inr α) + Finsupp.weight w α.val = d := by
      exact Nat.sub_add_cancel α.property.le
    rwa [hsum] at hh

end PolynomialTranslationLie
end Erdos3

end

end OAI
