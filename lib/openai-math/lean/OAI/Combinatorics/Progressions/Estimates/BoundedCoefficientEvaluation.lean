import OAI.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTermCount
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialEvaluationMass

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

theorem bounded_coefficients_evaluation_error {J : Type*} [Fintype J]
    (P Q : MvPolynomial J ℝ) {s : ℕ} (hP : P.totalDegree ≤ s) (hQ : Q.totalDegree ≤ s)
    {η B : ℝ} (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hcoeff : ∀ e : BoundedIntegerExponent J s, |P.coeff e.val - Q.coeff e.val| ≤ η)
    (x : J → ℝ) (hx : ∀ j, |x j| ≤ B) :
    |aeval x P - aeval x Q| ≤ ((s + 1) * (Fintype.card J + 1) ^ s : ℕ) * η * B ^ s := by
  have hdeg : (P - Q).totalDegree ≤ s := (totalDegree_sub P Q).trans (max_le hP hQ)
  have hmass : realPolynomialMass (P - Q) ≤ ((s + 1) * (Fintype.card J + 1) ^ s : ℕ) * η := by
    calc
      _ ≤ ∑ _e ∈ (P - Q).support, η := by
        apply Finset.sum_le_sum
        intro e he
        simpa only [coeff_sub] using hcoeff ⟨e, (le_totalDegree he).trans hdeg⟩
      _ = ((P - Q).support.card : ℝ) * η := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (polynomial_support_card_le _ hdeg)) hη
  rw [← map_sub]
  exact (abs_aeval_le_mass_box (P - Q) x hB hx hdeg).trans
    (mul_le_mul_of_nonneg_right hmass (pow_nonneg (zero_le_one.trans hB) s))

end Erdos3

end

end OAI
