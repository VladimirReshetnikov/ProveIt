import OAI.Combinatorics.Progressions.Geometry.TranslationShearCoordinateSeries
import OAI.Combinatorics.Progressions.Polynomial.TranslationParameterPolynomialPacking

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators

variable {U B : Type*}

private theorem pderiv_inr_rename_inl (i : B) (P : MvPolynomial U ℝ) :
    pderiv (Sum.inr i) (rename Sum.inl P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => simp [hp]

theorem packTranslationPolynomial_pderiv (Q : MvPolynomial B (MvPolynomial U ℝ)) (i : B) :
    packTranslationPolynomial (pderiv i Q) =
      pderiv (Sum.inr i) (packTranslationPolynomial Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C P => simp [pderiv_inr_rename_inl]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P j hP =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
      packTranslationPolynomial_X, hP, pderiv_X, Pi.single_apply]
    by_cases h : j = i <;> simp [h]

theorem packTranslationPolynomial_directional_sum [Fintype B]
    (b : B → MvPolynomial U ℝ) (Q : MvPolynomial B (MvPolynomial U ℝ)) :
    packTranslationPolynomial (∑ i, b i • pderiv i Q) =
      translationDirectionalDerivative b (packTranslationPolynomial Q) := by
  classical
  rw [translationDirectionalDerivative_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← MvPolynomial.C_mul', map_mul, packTranslationPolynomial_C,
    packTranslationPolynomial_pderiv]

theorem packTranslationPolynomial_baseDerivative [Fintype B]
    (b : B → MvPolynomial U ℝ) (Q : MvPolynomial B (MvPolynomial U ℝ)) :
    packTranslationPolynomial (translationBaseDerivative b Q) =
      translationDirectionalDerivative b (packTranslationPolynomial Q) := by
  rw [translationBaseDerivative_apply, packTranslationPolynomial_directional_sum]

theorem packTranslationPolynomial_baseDerivative_pow [Fintype B]
    (b : B → MvPolynomial U ℝ) (Q : MvPolynomial B (MvPolynomial U ℝ)) (k : ℕ) :
    packTranslationPolynomial (((translationBaseDerivative b).toLinearMap ^ k) Q) =
      ((translationDirectionalDerivative b) ^ k) (packTranslationPolynomial Q) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    change packTranslationPolynomial (translationBaseDerivative b
      (((translationBaseDerivative b).toLinearMap ^ k) Q)) = _
    rw [packTranslationPolynomial_baseDerivative, ih]

end Erdos3

end

end OAI
