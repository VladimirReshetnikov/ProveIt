import OAI.Combinatorics.Progressions.Nilpotent.WeightedTranslationRealBCHCoordinates

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped TensorProduct

theorem translationShear_derivation_rename_eq_zero
    {σ : Type*} {w : σ ⊕ Unit → ℕ}
    (D : PolynomialShearLieAlgebra w ℝ)
    (hD : ∀ i, D.val (X (Sum.inl i)) = 0) (P : MvPolynomial σ ℝ) :
    D.val (rename Sum.inl P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_zero]
  | mul_X P i hP =>
    simp only [map_mul, rename_X, D.val.leibniz, hD, hP, smul_zero, add_zero]

namespace PolynomialTranslationLie

variable {B : Type*} [Fintype B]

theorem bchRealTranslationHom_pure_base_of_shape
    (w : B → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d)
    (v : ℝ ⊗[ℚ] weightedSubalgebra w d) (b : B → ℝ)
    (hb : ∀ i, (realShearEmbedding w d v).val (X (Sum.inl i)) = C (b i))
    (hP : (realShearEmbedding w d v).val (X (Sum.inr ())) = 0) :
    bchRealTranslationHom w d hwd ⟨v⟩ = ⟨b, 0⟩ := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [bchRealTranslationHom_action]
  change (polynomialShearExpAut (realShearEmbedding w d v)).val = _
  have h := PolynomialTranslationGroupOver.action_eq_of_shape
    (polynomialShearExpAut (realShearEmbedding w d v)).val b 0
    (fun i => polynomialShearExp_X_of_derivation_eq_C _ _ _ (hb i)) ?_
  · simpa only [PolynomialTranslationGroupOver.actionElement, map_zero] using h.symm
  · change polynomialShearExp (realShearEmbedding w d v) (X (Sum.inr ())) = _
    simpa only [map_zero] using polynomialShearExp_X_of_derivation_eq_C
      (realShearEmbedding w d v) (Sum.inr ()) 0 (by simpa only [map_zero] using hP)

theorem bchRealTranslationHom_pure_polynomial_of_shape
    (w : B → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d)
    (v : ℝ ⊗[ℚ] weightedSubalgebra w d) (P : MvPolynomial B ℝ)
    (hb : ∀ i, (realShearEmbedding w d v).val (X (Sum.inl i)) = 0)
    (hP : (realShearEmbedding w d v).val (X (Sum.inr ())) = rename Sum.inl P) :
    bchRealTranslationHom w d hwd ⟨v⟩ = ⟨0, P⟩ := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [bchRealTranslationHom_action]
  change (polynomialShearExpAut (realShearEmbedding w d v)).val = _
  have hsq : ((realShearEmbedding w d v).val.toLinearMap ^ 2) (X (Sum.inr ())) = 0 := by
    change (realShearEmbedding w d v).val ((realShearEmbedding w d v).val (X (Sum.inr ()))) = 0
    rw [hP]
    exact translationShear_derivation_rename_eq_zero _ hb P
  have h := PolynomialTranslationGroupOver.action_eq_of_shape
    (polynomialShearExpAut (realShearEmbedding w d v)).val 0 P
    (fun i => polynomialShearExp_X_of_derivation_eq_C _ _ _
      (by simpa only [Pi.zero_apply, map_zero] using hb i))
    (by change polynomialShearExp _ _ = _
        rw [polynomialShearExp_eq_add_of_sq_eq_zero _ hsq, hP])
  simpa only [PolynomialTranslationGroupOver.actionElement, neg_zero,
    polynomialTranslate_zero_ring] using h.symm

end PolynomialTranslationLie
end Erdos3

end

end OAI
