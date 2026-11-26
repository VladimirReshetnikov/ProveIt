import IPRADerivations.Analysis.Series.BernoulliBounds
import Mathlib.NumberTheory.BernoulliPolynomials

/-!
# Identification of the original fixed-order Bernoulli coefficients

The coefficients already used by the arithmetic certificates are
the coefficients of the standard Bernoulli polynomial divided by
its factorial. The normalization is identified by the derivative
recurrence and zero mean, before any mesh results use it.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliCoefficients

open Finset
open BernoulliCoefficients (bc bc_deriv bc_mean)
open BernoulliBounds (bden bint bint_eq)

noncomputable def normalized (j : ℕ) : Polynomial ℚ :=
  ((Nat.factorial j : ℚ)⁻¹) • Polynomial.bernoulli j

theorem degree_le (j : ℕ) : (normalized j).natDegree ≤ j := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  simp [normalized,Polynomial.coeff_bernoulli,not_le_of_gt hi]

theorem normalized_derivative (j : ℕ) : (normalized (j+1)).derivative = normalized j := by
  unfold normalized
  rw [Polynomial.derivative_smul,Polynomial.derivative_bernoulli_add_one,← Nat.cast_one (R := Polynomial ℚ),
    ← Nat.cast_add,← Polynomial.C_eq_natCast,← Polynomial.smul_eq_C_mul,smul_smul]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hj : ((j+1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hf : (Nat.factorial j : ℚ) ≠ 0 := by positivity
  field_simp

theorem normalized_endpoint (j : ℕ) (hj : 2 ≤ j) : (normalized j).eval 1 = (normalized j).eval 0 := by
  have e := Polynomial.bernoulli_eval_one_add j 0
  have h : j-1 ≠ 0 := by omega
  simp [zero_pow h] at e
  simpa [normalized,smul_eq_mul] using congrArg ((Nat.factorial j : ℚ)⁻¹ * ·) e

theorem normalized_mean (j : ℕ) : ∑ i ∈ range (j+2), (normalized (j+1)).coeff i / ((i : ℚ)+1) = 0 := by
  have hc (i : ℕ) : (normalized (j+1)).coeff i / ((i : ℚ)+1) = (normalized (j+2)).coeff (i+1) := by
    rw [← normalized_derivative (j+1),Polynomial.coeff_derivative]
    have h : ((i : ℚ)+1) ≠ 0 := by positivity
    field_simp
  have e := normalized_endpoint (j+2) (by omega)
  have he : (normalized (j+2)).natDegree < j+3 := Nat.lt_of_le_of_lt (degree_le (j+2)) (by omega)
  rw [Polynomial.eval_eq_sum_range' he, ← Polynomial.coeff_zero_eq_eval_zero] at e
  simp only [one_pow,_root_.mul_one] at e
  rw [sum_range_succ'] at e
  simp_rw [hc]
  linarith [e]

theorem coefficient (j i : ℕ) : (normalized j).coeff i = bc j i := by
  induction j generalizing i with
  | zero =>
      simp [normalized,bc,Polynomial.coeff_one]
  | succ j ih =>
      have step (k : ℕ) : (normalized (j+1)).coeff (k+1) = bc (j+1) (k+1) := by
        have h := congrArg (fun P : Polynomial ℚ => P.coeff k) (normalized_derivative j)
        rw [Polynomial.coeff_derivative,ih k] at h
        have d := bc_deriv j k
        have hk : ((k : ℚ)+1) ≠ 0 := by positivity
        apply mul_left_cancel₀ hk
        linear_combination h-d
      cases i with
      | succ k => exact step k
      | zero =>
          have a := normalized_mean j
          have b := bc_mean j
          rw [sum_range_succ'] at a b
          simp_rw [step] at a
          simp only [Nat.cast_zero,_root_.zero_add,_root_.div_one] at a b
          linarith

theorem reflection (j : ℕ) (t : ℚ) :
    (normalized j).eval (1-t) = (-1)^j * (normalized j).eval t := by
  simp only [normalized,Polynomial.eval_smul,smul_eq_mul,Polynomial.bernoulli_eval_one_sub]
  ring

theorem odd_constant_zero {j : ℕ} (hj : Odd j) (h : 1 < j) : bc j 0 = 0 := by
  rw [← coefficient,Polynomial.coeff_zero_eq_eval_zero]
  simp [normalized,bernoulli_eq_zero_of_odd hj h]

theorem integer_polynomial_evaluation (j : ℕ) (t : ℚ) :
    (∑ i : Fin (j+1), (bint j i : ℚ)*t^(i : ℕ)) = (bden j : ℚ)*(normalized j).eval t := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr (degree_le j)),mul_sum,← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  rw [coefficient,bint_eq]
  ring

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderBernoulliCoefficients
