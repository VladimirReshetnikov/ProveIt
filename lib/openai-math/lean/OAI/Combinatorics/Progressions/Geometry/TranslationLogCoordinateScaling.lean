import OAI.Combinatorics.Progressions.Polynomial.TranslationPolynomialPackingDerivative
import OAI.Combinatorics.Progressions.Sampling.TranslationLogCoordinateInputGrid

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open MvPolynomial
open scoped BigOperators
variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem translationLogMixedGroupPolynomial_eq_series (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) :
    translationLogMixedGroupPolynomial w d x f =
      translationDirectionalSeries d (translationLogBasePolynomial w d x f)
        (packTranslationPolynomial (translationLogPhasePolynomial w d x f)) := by
  have hweights : ∀ i, shearWeight w d i ≤ d := by
    intro i
    cases i with
    | inl i => exact hwd i
    | inr i => exact le_rfl
  unfold translationLogMixedGroupPolynomial translationLogGroupPolynomial
  rw [translationShearCoordinates_polynomial_series (shearWeight w d) d hweights]
  simp only [shearWeight, translationDirectionalSeries, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_rat_smul, packTranslationPolynomial_baseDerivative_pow]
  rw [← algebraMap_smul ℝ ((-1 : ℚ) ^ k / ((k + 1).factorial : ℚ))]
  congr 1
  simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]

theorem realPolynomialMass_translationLogMixedGroupPolynomial (w : B → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {M B₀ : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀)
    (hf : ∀ k, realPolynomialMass (f k) ≤ M)
    (hbase : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀)
    (hphase : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (translationLogMixedGroupPolynomial w d x f) ≤
      ((d : ℝ) + 1) * ((Fintype.card κ : ℝ) * M * B₀) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card κ : ℝ) * M * B₀)) ^ d := by
  rw [translationLogMixedGroupPolynomial_eq_series w d hwd]
  exact realPolynomialMass_translationLogDirectionalSeries w d hw x f hM hB₀ hf hbase hphase

theorem translationLogMixedGroupPolynomial_coefficientGrid (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) {q : ℕ}
    (hb : ∀ i, realPolynomialCoefficientGrid q (translationLogBasePolynomial w d x f i))
    (hP : realPolynomialCoefficientGrid q
      (packTranslationPolynomial (translationLogPhasePolynomial w d x f))) :
    realPolynomialCoefficientGrid (d.factorial * q ^ (d + 1))
      (translationLogMixedGroupPolynomial w d x f) := by
  rw [translationLogMixedGroupPolynomial_eq_series w d hwd]
  exact translationDirectionalSeries_coefficientGrid d _ _ hb hP

theorem translationLogMixedGroupPolynomial_coefficientGrid_of_inputs
    (w : B → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    {q l : ℕ} (hf : ∀ k, realPolynomialCoefficientGrid q (f k))
    (hbase : ∀ k i, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * ((x k).val.base i : ℝ))
    (hphase : ∀ k, realPolynomialCoefficientGrid l
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial)) :
    realPolynomialCoefficientGrid (d.factorial * (q * l) ^ (d + 1))
      (translationLogMixedGroupPolynomial w d x f) := by
  rw [translationLogMixedGroupPolynomial_eq_series w d hwd]
  exact translationLogDirectionalSeries_coefficientGrid w d x f hf hbase hphase

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie
open MvPolynomial
open scoped BigOperators
variable {U B κ : Type*} [Fintype B] [Fintype κ]

theorem translationLogBasePolynomial_scale (w : B → ℕ) (d : ℕ)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    (H : U → ℝ) (i : B) :
    scaleMvPolynomialAxes H (translationLogBasePolynomial w d x f i) =
      translationLogBasePolynomial w d x (fun k => scaleMvPolynomialAxes H (f k)) i := by
  simp only [translationLogBasePolynomial, scaleMvPolynomialAxes_eq_aeval, map_sum,
    map_mul, aeval_C, algebraMap_eq]

theorem translationLogMixedGroupPolynomial_scale (w : B → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (x : κ → weightedSubalgebra w d)
    (f : κ → MvPolynomial U ℝ) (H : U → ℝ) :
    scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (translationLogMixedGroupPolynomial w d x f) =
    translationLogMixedGroupPolynomial w d x (fun k => scaleMvPolynomialAxes H (f k)) := by
  apply MvPolynomial.funext
  intro z
  let u : U → ℝ := fun i => z (Sum.inl i)
  let a : B → ℝ := fun i => z (Sum.inr i)
  have hz : z = Sum.elim u a := by funext i; cases i <;> rfl
  rw [hz, scaleMvPolynomialAxes_eval]
  have he : (fun i => Sum.elim H (fun _ : B => (1 : ℝ)) i * Sum.elim u a i) =
      Sum.elim (fun i => H i * u i) a := by
    funext i
    cases i <;> simp
  rw [he, translationLogMixedGroupPolynomial_eval w d hwd,
    translationLogMixedGroupPolynomial_eval w d hwd]
  simp only [scaleMvPolynomialAxes_eval]

theorem realPolynomialMass_translationLogMixedGroupPolynomial_scale
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : κ → weightedSubalgebra w d) (f : κ → MvPolynomial U ℝ)
    (H : U → ℝ) {M B₀ : ℝ} (hM : 0 ≤ M) (hB₀ : 0 ≤ B₀)
    (hf : ∀ k, realPolynomialMass (scaleMvPolynomialAxes H (f k)) ≤ M)
    (hbase : ∀ k i, |((x k).val.base i : ℝ)| ≤ B₀)
    (hphase : ∀ k, realPolynomialMass
      (MvPolynomial.map (algebraMap ℚ ℝ) (x k).val.polynomial) ≤ B₀) :
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim H (fun _ : B => 1))
      (translationLogMixedGroupPolynomial w d x f)) ≤
      ((d : ℝ) + 1) * ((Fintype.card κ : ℝ) * M * B₀) *
        (1 + (Fintype.card B : ℝ) * d * ((Fintype.card κ : ℝ) * M * B₀)) ^ d := by
  rw [translationLogMixedGroupPolynomial_scale w d hwd]
  exact realPolynomialMass_translationLogMixedGroupPolynomial w d hw hwd x _
    hM hB₀ hf hbase hphase

end Erdos3.PolynomialTranslationLie

end

end OAI
