import OAI.Combinatorics.Progressions.Polynomial.TranslationLogCoordinatePolynomials

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

theorem packTranslationPolynomial_map_C {U B R : Type*} [CommSemiring R]
    (P : MvPolynomial B R) :
    packTranslationPolynomial (U := U) (MvPolynomial.map C P) = rename Sum.inr P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, map_X, packTranslationPolynomial_X, rename_X, hP]

namespace PolynomialTranslationLie

variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem pack_translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    packTranslationPolynomial (translationLogPhasePolynomial w d x f) =
      ∑ k, rename Sum.inl (f k) *
        rename Sum.inr (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) := by
  classical
  unfold translationLogPhasePolynomial
  simp only [map_sum, map_mul, packTranslationPolynomial_C]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [← MvPolynomial.map_map, packTranslationPolynomial_map_C]

theorem realPolynomialMass_translationLogBasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {M B₀ : ℝ} (hM : 0 ≤ M) (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hx : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀) (i : B) :
    realPolynomialMass (translationLogBasePolynomial w d x f i) ≤
      (Fintype.card κ : ℝ) * M * B₀ := by
  classical
  unfold translationLogBasePolynomial
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : κ, M * B₀ := by
      apply Finset.sum_le_sum
      intro k _
      apply (realPolynomialMass_mul_le _ _).trans
      rw [realPolynomialMass_C]
      exact mul_le_mul (hf k) (hx k i) (abs_nonneg _) hM
    _ = _ := by simp; ring

theorem realPolynomialMass_pack_translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {M B₀ : ℝ} (hM : 0 ≤ M) (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hx : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (packTranslationPolynomial (translationLogPhasePolynomial w d x f)) ≤
      (Fintype.card κ : ℝ) * M * B₀ := by
  classical
  rw [pack_translationLogPhasePolynomial]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : κ, M * B₀ := by
      apply Finset.sum_le_sum
      intro k _
      exact (realPolynomialMass_mul_le _ _).trans
        (mul_le_mul ((realPolynomialMass_rename_le _ _).trans (hf k))
          ((realPolynomialMass_rename_le _ _).trans (hx k)) (realPolynomialMass_nonneg _) hM)
    _ = _ := by simp; ring

theorem weightedSubalgebra_realPolynomial_degreeOf_le (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : weightedSubalgebra w d) (i : B) :
    (MvPolynomial.map (algebraMap ℚ ℝ) x.val.polynomial).degreeOf i ≤ d := by
  classical
  rw [degreeOf_eq_sup]
  apply Finset.sup_le
  intro α hα
  have hs := MvPolynomial.support_map_subset (algebraMap ℚ ℝ) x.val.polynomial hα
  have hx := x.property.2 hs
  change Finsupp.weight w α + 1 ≤ d at hx
  have hαi := Finsupp.le_weight w (hw i).ne' α
  exact hαi.trans (by omega)

theorem degreeOf_pack_translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (i : B) :
    (packTranslationPolynomial (translationLogPhasePolynomial w d x f)).degreeOf
      (Sum.inr i) ≤ d := by
  classical
  rw [pack_translationLogPhasePolynomial]
  apply (degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro k _
  apply (degreeOf_mul_le _ _ _).trans
  rw [degreeOf_rename_inl_inr, zero_add,
    degreeOf_rename_of_injective Sum.inr_injective i]
  exact weightedSubalgebra_realPolynomial_degreeOf_le w d hw (x k) i

theorem realPolynomialMass_translationLogDirectionalSeries (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) {M B₀ : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀)
    (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hbase : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀)
    (hphase : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (translationDirectionalSeries d (translationLogBasePolynomial w d x f)
      (packTranslationPolynomial (translationLogPhasePolynomial w d x f))) ≤
      ((d : ℝ) + 1) * ((Fintype.card κ : ℝ) * M * B₀) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card κ : ℝ) * M * B₀)) ^ d := by
  exact realPolynomialMass_translationDirectionalSeries d _ _
    (degreeOf_pack_translationLogPhasePolynomial w d hw x f) (by positivity)
    (realPolynomialMass_translationLogBasePolynomial w d x f hM hf hbase)
    (realPolynomialMass_pack_translationLogPhasePolynomial w d x f hM hf hphase)

end PolynomialTranslationLie
end Erdos3

end

end OAI
