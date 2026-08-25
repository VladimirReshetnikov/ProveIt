import FabiusFunction.FabiusSaddleJetClosedForm

/-!
# The jet weights are Stirling numbers of the first kind

`FabiusSaddleJetClosedForm` introduces the weights `negativeLaplaceJetStirling`
by the recurrence that the induction there needs.  This module identifies them
with the coefficients of the falling-factorial polynomial

`∏ k ∈ Finset.range n, (X - (k + 1)) = (X - 1)(X - 2) ⋯ (X - n)`,

that is, with the signed Stirling numbers of the first kind.  The identification
is exactly the statement that the recurrence

`c (n+1) 0 = -(n+1) * c n 0`,
`c (n+1) (m+1) = c n m - (n+1) * c n (m+1)`

is the coefficient recurrence of multiplying a polynomial by `X - (n+1)`.

This is the structural reason for the shape of the closed-form jets: applying
the commuting operator product `∏ k ∈ Finset.range n, (D / log 2 - (k+1))` to
`1/2 + Psi' / log 2` distributes over the operator polynomial's coefficients,
and those coefficients are what this module names.
-/

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Fabius

noncomputable section

/-- The falling-factorial polynomial `(X - 1)(X - 2) ⋯ (X - n)`, presented by
the recurrence that matches `negativeLaplaceJetStirling`. -/
def negativeLaplaceJetPolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => negativeLaplaceJetPolynomial n * (X - C ((n : ℝ) + 1))

@[simp] theorem negativeLaplaceJetPolynomial_zero :
    negativeLaplaceJetPolynomial 0 = 1 := rfl

/-- One step of the falling-factorial recurrence. -/
theorem negativeLaplaceJetPolynomial_succ (n : ℕ) :
    negativeLaplaceJetPolynomial (n + 1) =
      negativeLaplaceJetPolynomial n * (X - C ((n : ℝ) + 1)) := rfl

/-- The falling-factorial polynomial as an explicit product. -/
theorem negativeLaplaceJetPolynomial_eq_prod (n : ℕ) :
    negativeLaplaceJetPolynomial n =
      ∏ k ∈ Finset.range n, (X - C ((k : ℝ) + 1)) := by
  induction n with
  | zero => rw [negativeLaplaceJetPolynomial_zero, Finset.prod_range_zero]
  | succ n ih =>
      rw [negativeLaplaceJetPolynomial_succ, ih, Finset.prod_range_succ]

/-- **The jet weights are signed Stirling numbers of the first kind.** -/
theorem negativeLaplaceJetStirling_eq_coeff (n m : ℕ) :
    negativeLaplaceJetStirling n m =
      (negativeLaplaceJetPolynomial n).coeff m := by
  induction n generalizing m with
  | zero =>
      cases m with
      | zero =>
          rw [negativeLaplaceJetStirling_zero_zero,
            negativeLaplaceJetPolynomial_zero, Polynomial.coeff_one_zero]
      | succ m =>
          rw [negativeLaplaceJetStirling_zero_succ,
            negativeLaplaceJetPolynomial_zero, Polynomial.coeff_one,
            if_neg (Nat.succ_ne_zero m)]
  | succ n ih =>
      cases m with
      | zero =>
          rw [negativeLaplaceJetStirling_succ_zero, ih 0,
            negativeLaplaceJetPolynomial_succ, Polynomial.mul_coeff_zero,
            Polynomial.coeff_sub, Polynomial.coeff_X_zero,
            Polynomial.coeff_C_zero]
          ring
      | succ m =>
          rw [negativeLaplaceJetStirling_succ_succ, ih m, ih (m + 1),
            negativeLaplaceJetPolynomial_succ,
            Polynomial.coeff_mul_X_sub_C]
          ring

/-- The falling-factorial polynomial is monic. -/
theorem negativeLaplaceJetPolynomial_monic (n : ℕ) :
    (negativeLaplaceJetPolynomial n).Monic := by
  induction n with
  | zero => rw [negativeLaplaceJetPolynomial_zero]; exact monic_one
  | succ n ih =>
      rw [negativeLaplaceJetPolynomial_succ]
      exact ih.mul (monic_X_sub_C _)

/-- The falling-factorial polynomial has degree `n`. -/
theorem negativeLaplaceJetPolynomial_natDegree (n : ℕ) :
    (negativeLaplaceJetPolynomial n).natDegree = n := by
  induction n with
  | zero => rw [negativeLaplaceJetPolynomial_zero, natDegree_one]
  | succ n ih =>
      rw [negativeLaplaceJetPolynomial_succ,
        (negativeLaplaceJetPolynomial_monic n).natDegree_mul (monic_X_sub_C _),
        ih, natDegree_X_sub_C]

/-- Closed form of the periodic saddle jets, with the weights displayed as
coefficients of the falling-factorial polynomial. -/
theorem negativeLaplacePeriodicJet_eq_polynomial_closedForm (n : ℕ) (t : ℝ) :
    negativeLaplacePeriodicJet n t =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) *
          (1 / 2 + ((harmonic n : ℚ) : ℝ) / Real.log 2) +
        ∑ m ∈ Finset.range (n + 1),
          (negativeLaplaceJetPolynomial n).coeff m *
            (iteratedDeriv (m + 1) negativeLaplacePsi t /
              Real.log 2 ^ (m + 1)) := by
  rw [negativeLaplacePeriodicJet_eq_closedForm n t]
  unfold negativeLaplaceJetConstant negativeLaplaceJetDerivativeSum
    negativeLaplacePsiScaledDeriv
  congr 1
  exact Finset.sum_congr rfl fun m _ => by
    rw [negativeLaplaceJetStirling_eq_coeff n m]

/-- Closed form of the bounded exponent jets, with the weights displayed as
coefficients of the falling-factorial polynomial. -/
theorem negativeLaplaceBoundedExponentJet_eq_polynomial_closedForm
    (n : ℕ) (t : ℝ) :
    negativeLaplaceBoundedExponentJet n t =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) *
          (((harmonic n : ℚ) : ℝ) / Real.log 2 - 1 / 2) +
        ∑ m ∈ Finset.range (n + 1),
          (negativeLaplaceJetPolynomial n).coeff m *
            (iteratedDeriv (m + 1) negativeLaplacePsi t /
              Real.log 2 ^ (m + 1)) := by
  rw [negativeLaplaceBoundedExponentJet_eq_closedForm n t]
  unfold negativeLaplaceJetDerivativeSum negativeLaplacePsiScaledDeriv
  congr 1
  exact Finset.sum_congr rfl fun m _ => by
    rw [negativeLaplaceJetStirling_eq_coeff n m]

end

end Fabius
