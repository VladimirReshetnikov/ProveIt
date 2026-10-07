import OAI.Combinatorics.Progressions.Estimates.CoefficientModeLowerTerms

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def factorialContractedRow {K J : Type*} [Fintype K] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ) : J → ℤ :=
  fun j => (h.factorial : ℤ) * integerContractedRow frequency (∏ i, rowPolynomial (a i)) j

theorem factorialContractedRow_eval {I K J : Type*} [Fintype K] [Fintype J] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (w : I → ℝ) :
    MvPolynomial.eval w (integerRowPolynomial (factorialContractedRow frequency a) p) =
      (h.factorial : ℝ) * ∑ j,
        (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * eval w p j := by
  simp [integerRowPolynomial_eval, factorialContractedRow, Finset.mul_sum, mul_assoc]

theorem coefficientMode_diagonal_polynomial {I K J : Type*} [Fintype K] [Fintype J] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ)
    (p : VectorPolynomial I ℝ (J → ℝ)) (hp : Homogeneous h p) (w : I → ℝ) :
    MvPolynomial.eval w (integerRowPolynomial (factorialContractedRow frequency a) p) =
      polynomialTopSymbol h (coefficientModePolynomial
        (coefficientFunctional (fun d j => (frequency d j : ℝ))) p)
        (fun i z => (a i z.1 : ℝ) * w z.2) := by
  rw [factorialContractedRow_eval]
  exact (coefficientModePolynomial_top_integer_row frequency p hp a w).symm

theorem factorialContractedRow_bound {K J : Type*} [Fintype K] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ) {B : ℝ}
    (hb : ∀ j, |(integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ)| ≤ B) :
    ∀ j, |(factorialContractedRow frequency a j : ℝ)| ≤ (h.factorial : ℝ) * B := by
  intro j
  simpa only [factorialContractedRow, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg h.factorial : (0 : ℝ) ≤ _)] using
    mul_le_mul_of_nonneg_left (hb j) (Nat.cast_nonneg h.factorial : (0 : ℝ) ≤ _)

theorem factorialContractedRow_nonzero {K J : Type*} [Fintype K] [Fintype J] {h : ℕ}
    (frequency : (K →₀ ℕ) → J → ℤ) (a : Fin h → K → ℤ) (w : J → ℝ)
    (hw : (∑ j, (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w j) ≠ 0) :
    (∑ j, (factorialContractedRow frequency a j : ℝ) * w j) ≠ 0 := by
  have he : (∑ j, (factorialContractedRow frequency a j : ℝ) * w j) =
      (h.factorial : ℝ) * ∑ j,
        (integerContractedRow frequency (∏ i, rowPolynomial (a i)) j : ℝ) * w j := by
    simp [factorialContractedRow, Finset.mul_sum, mul_assoc]
  rw [he]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h)) hw

end Erdos3.VectorPolynomial

end

end OAI
