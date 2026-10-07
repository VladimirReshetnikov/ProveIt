import OAI.Combinatorics.Progressions.Geometry.TranslationShearCoordinateSeries
import OAI.Combinatorics.Progressions.Nilpotent.WeightedTranslationRealBCHCoordinates
import OAI.Combinatorics.Progressions.Polynomial.TranslationParameterPolynomialPacking

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial
open scoped BigOperators TensorProduct

variable {U B κ : Type*} [Fintype B] [Fintype κ]

private theorem shear_sum_apply {S I : Type*} [CommRing S] {w : I → ℕ}
    (D : κ → PolynomialShearLieAlgebra w S) (P : MvPolynomial I S) :
    (∑ k, D k).val P = ∑ k, (D k).val P := by
  classical
  have h (t : Finset κ) : (∑ k ∈ t, D k).val P = ∑ k ∈ t, (D k).val P := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert k t hk ih =>
      simp only [Finset.sum_insert hk]
      change (D k).val P + (∑ k ∈ t, D k).val P = _
      rw [ih]
  exact h Finset.univ

noncomputable def translationLogPolynomialShear (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    PolynomialShearLieAlgebra (shearWeight w d) (MvPolynomial U ℝ) :=
  ∑ k, f k • polynomialShearMap (MvPolynomial.C.comp (algebraMap ℚ ℝ))
    (weightedShearEmbedding w d (x k))

noncomputable def translationLogBasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) (i : B) :
    MvPolynomial U ℝ := ∑ k, f k * C ((x k).val.base i : ℝ)

noncomputable def translationLogPhasePolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    MvPolynomial B (MvPolynomial U ℝ) :=
  ∑ k, C (f k) * MvPolynomial.map (MvPolynomial.C.comp (algebraMap ℚ ℝ))
    (x k).val.polynomial

theorem translationLogPolynomialShear_base (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) (i : B) :
    (translationLogPolynomialShear w d x f).val (X (Sum.inl i)) =
      C (translationLogBasePolynomial w d x f i) := by
  classical
  simp only [translationLogPolynomialShear, translationLogBasePolynomial,
    shear_sum_apply, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro k _
  change f k • (polynomialShearMap ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (weightedShearEmbedding w d (x k))).val (X (Sum.inl i)) = _
  rw [polynomialShearMap_X]
  change f k • MvPolynomial.map ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (shearDerivation (x k).val (X (Sum.inl i))) = _
  rw [shearDerivation_X_inl, map_C]
  rw [← MvPolynomial.C_mul']
  rfl

theorem translationLogPolynomialShear_phase (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    (translationLogPolynomialShear w d x f).val (X (Sum.inr ())) =
      rename Sum.inl (translationLogPhasePolynomial w d x f) := by
  classical
  simp only [translationLogPolynomialShear, translationLogPhasePolynomial,
    shear_sum_apply, map_sum, map_mul, rename_C]
  apply Finset.sum_congr rfl
  intro k _
  change f k • (polynomialShearMap ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (weightedShearEmbedding w d (x k))).val (X (Sum.inr ())) = _
  rw [polynomialShearMap_X]
  change f k • MvPolynomial.map ((C (σ := U)).comp (algebraMap ℚ ℝ))
    (shearDerivation (x k).val (X (Sum.inr ()))) = _
  rw [shearDerivation_X_inr, MvPolynomial.map_rename]
  exact MvPolynomial.C_mul'.symm

theorem translationLogPolynomialShear_specialize (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) (u : U → ℝ) :
    polynomialShearMap (MvPolynomial.eval u) (translationLogPolynomialShear w d x f) =
      realShearEmbedding w d (∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k) := by
  classical
  have hc : (MvPolynomial.eval u).comp (C.comp (algebraMap ℚ ℝ)) = algebraMap ℚ ℝ := by
    ext r
    simp
  simp only [translationLogPolynomialShear, polynomialShearMap_sum, polynomialShearMap_smul,
    polynomialShearMap_comp, hc, map_sum, realShearEmbedding_tmul]

noncomputable def translationLogGroupPolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    PolynomialTranslationGroupOver (MvPolynomial U ℝ) B :=
  translationShearCoordinates (translationLogPolynomialShear w d x f)
    (translationLogBasePolynomial w d x f) (translationLogPhasePolynomial w d x f)
    (translationLogPolynomialShear_base w d x f) (translationLogPolynomialShear_phase w d x f)

theorem translationLogGroupPolynomial_base (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    (translationLogGroupPolynomial w d x f).base = translationLogBasePolynomial w d x f :=
  translationShearCoordinates_base _ _ _ _ _

theorem translationLogGroupPolynomial_specialize (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (u : U → ℝ) :
    PolynomialTranslationGroupOver.map (MvPolynomial.eval u) (translationLogGroupPolynomial w d x f) =
      bchRealTranslationHom w d hwd
        ⟨∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k⟩ := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [translationLogGroupPolynomial, translationShearCoordinates_map_action,
    bchRealTranslationHom_action, weightedShearRealGroupHom_apply]
  rw [translationLogPolynomialShear_specialize]
  rfl

noncomputable def translationLogMixedGroupPolynomial (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ) :
    MvPolynomial (U ⊕ B) ℝ :=
  packTranslationPolynomial (translationLogGroupPolynomial w d x f).polynomial

theorem translationLogMixedGroupPolynomial_specialize (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (u : U → ℝ) :
    aeval (Sum.elim (fun i => C (u i)) X)
      (translationLogMixedGroupPolynomial w d x f) =
      (bchRealTranslationHom w d hwd
        ⟨∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k⟩).polynomial := by
  rw [translationLogMixedGroupPolynomial, packTranslationPolynomial_specialize]
  exact congrArg PolynomialTranslationGroupOver.polynomial
    (translationLogGroupPolynomial_specialize w d hwd x f u)

theorem translationLogMixedGroupPolynomial_eval (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (u : U → ℝ) (a : B → ℝ) :
    eval (Sum.elim u a) (translationLogMixedGroupPolynomial w d x f) =
      eval a (bchRealTranslationHom w d hwd
        ⟨∑ k, (MvPolynomial.eval u (f k)) ⊗ₜ[ℚ] x k⟩).polynomial := by
  rw [translationLogMixedGroupPolynomial, packTranslationPolynomial_eval]
  congr 1
  exact congrArg PolynomialTranslationGroupOver.polynomial
    (translationLogGroupPolynomial_specialize w d hwd x f u)

end Erdos3.PolynomialTranslationLie

end

end OAI
