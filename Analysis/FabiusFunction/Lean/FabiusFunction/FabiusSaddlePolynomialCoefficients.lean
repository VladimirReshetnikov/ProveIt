import FabiusFunction.PeriodicSmooth
import FabiusFunction.SaddleExpansionAlgebra

/-!
# Polynomial coefficients for the all-orders Fabius saddle expansion

The concrete exponent coefficient from
`FabiusSaddleCoefficientRecurrence` is polynomial in the Gaussian variable.
This module packages it as an element of `Polynomial ℂ`, making it directly
usable by the generic `SaddleExpansion.expCoeff` recurrence.

Coefficientwise complex conjugation acts on the exponent polynomial of order
`m` by the sign `(-1)^m`.  Functoriality and rescaling of `expCoeff` propagate
this identity to every exponential coefficient; in particular every even
coefficient is fixed by conjugation and every odd coefficient is negated.
Evaluation at `-v` has the matching sign, while evaluation at the Gaussian
origin vanishes at every exponent order.
-/

set_option autoImplicit false

open Complex Polynomial

namespace Fabius

open SaddleExpansion

/-- The polynomial in the centered Gaussian variable multiplying
`epsilon^m` in the central saddle exponent. -/
noncomputable def negativeLaplaceExponentPolynomial
    (m : ℕ) (t : ℝ) : Polynomial ℂ :=
  match m with
  | 0 => 0
  | n + 1 =>
      C (I ^ (n + 1) * (negativeLaplaceBoundedExponentJet n t : ℂ) /
          ((n + 1).factorial : ℕ)) * X ^ (n + 1) +
        C (I ^ (n + 3) * (negativeLaplaceJetSlope (n + 2) : ℂ) /
          ((n + 3).factorial : ℕ)) * X ^ (n + 3)

/-- The negative-Laplace exponent polynomial vanishes at order zero. -/
@[simp] theorem negativeLaplaceExponentPolynomial_zero (t : ℝ) :
    negativeLaplaceExponentPolynomial 0 t = 0 := by
  rfl

/-- Evaluation at a real Gaussian variable recovers the scalar exponent
coefficient. -/
theorem negativeLaplaceExponentPolynomial_eval
    (m : ℕ) (t v : ℝ) :
    (negativeLaplaceExponentPolynomial m t).eval (v : ℂ) =
      negativeLaplaceExponentCoefficient m t v := by
  cases m with
  | zero => simp [negativeLaplaceExponentPolynomial,
      negativeLaplaceExponentCoefficient]
  | succ n =>
      simp only [negativeLaplaceExponentPolynomial,
        negativeLaplaceExponentCoefficient, eval_add, eval_mul,
        eval_C, eval_X, eval_pow]
      ring

/-- Evaluation of an order-`m` exponent polynomial at `-v` differs from its
value at `v` by the parity sign `(-1)^m`. -/
theorem negativeLaplaceExponentPolynomial_eval_neg
    (m : ℕ) (t : ℝ) (v : ℂ) :
    (negativeLaplaceExponentPolynomial m t).eval (-v) =
      (-1 : ℂ) ^ m *
        (negativeLaplaceExponentPolynomial m t).eval v := by
  cases m with
  | zero => simp [negativeLaplaceExponentPolynomial]
  | succ n =>
      simp only [negativeLaplaceExponentPolynomial, eval_add, eval_mul,
        eval_C, eval_X, eval_pow]
      rw [show (-v) ^ (n + 1) =
          (-1 : ℂ) ^ (n + 1) * v ^ (n + 1) by rw [neg_pow]]
      rw [show (-v) ^ (n + 3) =
          (-1 : ℂ) ^ (n + 3) * v ^ (n + 3) by rw [neg_pow]]
      rw [show (-1 : ℂ) ^ (n + 3) = (-1 : ℂ) ^ (n + 1) by
        rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
        norm_num]
      ring

/-- Every exponent polynomial vanishes at the Gaussian origin. -/
theorem negativeLaplaceExponentPolynomial_eval_zero (m : ℕ) (t : ℝ) :
    (negativeLaplaceExponentPolynomial m t).eval 0 = 0 := by
  change (negativeLaplaceExponentPolynomial m t).eval ((0 : ℝ) : ℂ) = 0
  rw [negativeLaplaceExponentPolynomial_eval,
    negativeLaplaceExponentCoefficient_at_zero]

/-- Every exponent polynomial is one-periodic in the saddle phase. -/
theorem negativeLaplaceExponentPolynomial_periodic (m : ℕ) :
    Function.Periodic (negativeLaplaceExponentPolynomial m) 1 := by
  intro t
  cases m with
  | zero => rfl
  | succ n =>
      simp only [negativeLaplaceExponentPolynomial]
      rw [negativeLaplaceBoundedExponentJet_periodic n t]

/-- Conjugating every coefficient of the order-`m` exponent polynomial
multiplies it by `(-1)^m`. -/
theorem negativeLaplaceExponentPolynomial_conj
    (m : ℕ) (t : ℝ) :
    (negativeLaplaceExponentPolynomial m t).map (starRingEnd ℂ) =
      (-1 : ℂ) ^ m • negativeLaplaceExponentPolynomial m t := by
  cases m with
  | zero => simp [negativeLaplaceExponentPolynomial]
  | succ n =>
      apply Polynomial.funext
      intro z
      simp [negativeLaplaceExponentPolynomial, Complex.conj_I,
        smul_add, smul_eq_C_mul]
      rw [show (-I) ^ (n + 1) =
          (-1 : ℂ) ^ (n + 1) * I ^ (n + 1) by rw [neg_pow]]
      rw [show (-I) ^ (n + 3) =
          (-1 : ℂ) ^ (n + 3) * I ^ (n + 3) by rw [neg_pow]]
      rw [show (-1 : ℂ) ^ (n + 3) = (-1 : ℂ) ^ (n + 1) by
        rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
        norm_num]
      ring

/-- The exponential coefficient of order `n` inherits conjugation parity
`(-1)^n` from the exponent polynomials. -/
theorem negativeLaplaceExpCoeff_conj
    (n : ℕ) (t : ℝ) :
    (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n).map
        (starRingEnd ℂ) =
      (-1 : ℂ) ^ n •
        expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n := by
  let conjAlg : Polynomial ℂ →ₐ[ℚ] Polynomial ℂ :=
    Polynomial.mapAlgHom (Complex.conjAe.restrictScalars ℚ)
  let E : ℕ → Polynomial ℂ := fun m =>
    negativeLaplaceExponentPolynomial m t
  have hE : (fun j => conjAlg (E j)) =
      fun j => (-1 : Polynomial ℂ) ^ j * E j := by
    funext j
    change (E j).map (starRingEnd ℂ) = _
    rw [show (E j).map (starRingEnd ℂ) =
        (-1 : ℂ) ^ j • E j by
      exact negativeLaplaceExponentPolynomial_conj j t]
    simp [smul_eq_C_mul]
  change conjAlg (expCoeff E n) = _
  calc
    conjAlg (expCoeff E n) =
        expCoeff (fun j => conjAlg (E j)) n :=
      map_expCoeff conjAlg E n
    _ = expCoeff (fun j => (-1 : Polynomial ℂ) ^ j * E j) n := by
      rw [hE]
    _ = (-1 : Polynomial ℂ) ^ n * expCoeff E n :=
      expCoeff_rescale (-1 : Polynomial ℂ) E n
    _ = (-1 : ℂ) ^ n • expCoeff E n := by
      simp [smul_eq_C_mul]

/-- Every exponential coefficient polynomial is one-periodic in the saddle
phase. -/
theorem negativeLaplaceExpCoeff_periodic (n : ℕ) :
    Function.Periodic
      (fun t : ℝ =>
        expCoeff (fun m => negativeLaplaceExponentPolynomial m t) n) 1 := by
  intro t
  apply expCoeff_congr n
  intro j _hj
  exact negativeLaplaceExponentPolynomial_periodic j t

/-- Every odd exponential coefficient is negated by coefficientwise complex
conjugation.  This complements the even fixed-point theorem below. -/
theorem negativeLaplaceExpCoeff_odd_conj (n : ℕ) (t : ℝ) :
    (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) (2 * n + 1)).map
        (starRingEnd ℂ) =
      -expCoeff (fun m => negativeLaplaceExponentPolynomial m t) (2 * n + 1) := by
  simpa [pow_add, pow_mul] using
    negativeLaplaceExpCoeff_conj (2 * n + 1) t

/-- Every even exponential coefficient is fixed by coefficientwise complex
conjugation. -/
theorem negativeLaplaceExpCoeff_even_conj (n : ℕ) (t : ℝ) :
    (expCoeff (fun m => negativeLaplaceExponentPolynomial m t) (2 * n)).map
        (starRingEnd ℂ) =
      expCoeff (fun m => negativeLaplaceExponentPolynomial m t) (2 * n) := by
  rw [negativeLaplaceExpCoeff_conj]
  norm_num [pow_mul]

end Fabius
