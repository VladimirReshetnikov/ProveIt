import FabiusFunction.ThueMorseFourierInversion
import FabiusFunction.ThueMorseValuation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Parseval mass of the Thue–Morse trigonometric polynomial

The characters `e^(2πinx)` are orthonormal on `[0,1]`, so the squared
modulus of the Thue–Morse trigonometric polynomial integrates to the
number of terms — the Parseval identity giving the Riesz density its
unit mass.

* `integral_exp_two_pi_int` — orthonormality:
  `∫₀¹ e^(2πi·d·x) dx = [d = 0]` for `d : ℤ`.
* `integral_thueMorse_double_sum` — **Parseval**:
  `∫₀¹ (∑_{n<2^m} ε(n)e^(2πinx))·(∑_{n'<2^m} ε(n')e^(-2πin'x)) dx = 2^m`.
  The second factor is the complex conjugate of the first on the real
  line, so this is `∫₀¹ |P_m(e^(2πix))|² dx = 2^m` — the mass
  `∫₀¹ ρ_m = 1` for the normalized Riesz density.
-/

set_option autoImplicit false

open Finset intervalIntegral

namespace Fabius

/-- Character orthonormality on `[0,1]`:
`∫₀¹ e^(2πi·d·x) dx = [d = 0]` for every integer `d`. -/
theorem integral_exp_two_pi_int (d : ℤ) :
    ∫ x in (0 : ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * d * x) =
      if d = 0 then 1 else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp
  · rw [if_neg hd]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hd' : (d : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd
    have hc : (2 * (Real.pi : ℂ) * Complex.I * d : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ)
        Complex.I_ne_zero) hd'
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero]
    rw [Complex.exp_zero,
      show (2 * (Real.pi : ℂ) * Complex.I * d : ℂ) =
        (d : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]

/-- **Parseval for the Thue–Morse block.**  The product of the
trigonometric polynomial with its reflected conjugate integrates over a
period to the number of terms:
`∫₀¹ (∑ ε(n)e^(2πinx))·(∑ ε(n')e^(-2πin'x)) dx = 2^m`, that is,
`∫₀¹ |P_m(e^(2πix))|² dx = 2^m` and the Riesz density has unit mass. -/
theorem integral_thueMorse_double_sum (m : ℕ) :
    ∫ x in (0 : ℝ)..1,
        (∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * n * x)) *
          (∑ n' ∈ range (2 ^ m), ((thueMorseSign n' : ℤ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * n' * x))) =
      ((2 ^ m : ℕ) : ℂ) := by
  have hcont : ∀ c : ℂ,
      Continuous (fun x : ℝ => Complex.exp (c * x)) := by
    intro c
    exact Complex.continuous_exp.comp (continuous_const.mul
      Complex.continuous_ofReal)
  have hpoint : ∀ x : ℝ,
      (∑ n ∈ range (2 ^ m), ((thueMorseSign n : ℤ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * x)) *
        (∑ n' ∈ range (2 ^ m), ((thueMorseSign n' : ℤ) : ℂ) *
          Complex.exp (-(2 * Real.pi * Complex.I * n' * x))) =
      ∑ n ∈ range (2 ^ m), ∑ n' ∈ range (2 ^ m),
        (((thueMorseSign n : ℤ) : ℂ) * ((thueMorseSign n' : ℤ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I *
            (((n : ℤ) - (n' : ℤ) : ℤ) : ℂ) * x) := by
    intro x
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl
      fun n' _ => ?_
    have hexp : Complex.exp (2 * Real.pi * Complex.I * n * x) *
        Complex.exp (-(2 * Real.pi * Complex.I * n' * x)) =
        Complex.exp (2 * Real.pi * Complex.I *
          (((n : ℤ) - (n' : ℤ) : ℤ) : ℂ) * x) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc ((thueMorseSign n : ℤ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * x) *
          (((thueMorseSign n' : ℤ) : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I * n' * x)))
        = (((thueMorseSign n : ℤ) : ℂ) * ((thueMorseSign n' : ℤ) : ℂ)) *
            (Complex.exp (2 * Real.pi * Complex.I * n * x) *
              Complex.exp (-(2 * Real.pi * Complex.I * n' * x))) := by
          ring
      _ = (((thueMorseSign n : ℤ) : ℂ) * ((thueMorseSign n' : ℤ) : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I *
              (((n : ℤ) - (n' : ℤ) : ℤ) : ℂ) * x) := by
          rw [hexp]
  rw [intervalIntegral.integral_congr
    (g := fun x : ℝ => ∑ n ∈ range (2 ^ m), ∑ n' ∈ range (2 ^ m),
      (((thueMorseSign n : ℤ) : ℂ) * ((thueMorseSign n' : ℤ) : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I *
          (((n : ℤ) - (n' : ℤ) : ℤ) : ℂ) * x))
    (fun x _ => hpoint x)]
  have hintegrable : ∀ (c₁ c₂ : ℂ),
      IntervalIntegrable (fun x : ℝ => c₁ * Complex.exp (c₂ * x))
        MeasureTheory.volume 0 1 :=
    fun c₁ c₂ => (Continuous.mul continuous_const (hcont c₂)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_finsetSum]
  swap
  · intro n _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro n' _
    exact Continuous.mul continuous_const (hcont _)
  have hrow : ∀ n ∈ range (2 ^ m),
      (∫ x in (0:ℝ)..1, ∑ n' ∈ range (2 ^ m),
        (((thueMorseSign n : ℤ) : ℂ) * ((thueMorseSign n' : ℤ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I *
            (((n : ℤ) - (n' : ℤ) : ℤ) : ℂ) * x)) = 1 := by
    intro n hn
    rw [intervalIntegral.integral_finsetSum]
    swap
    · intro n' _
      exact hintegrable _ _
    have hterm : ∀ n' ∈ range (2 ^ m),
        (∫ x in (0:ℝ)..1,
          (((thueMorseSign n : ℤ) : ℂ) * ((thueMorseSign n' : ℤ) : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I *
              (((n : ℤ) - (n' : ℤ) : ℤ) : ℂ) * x)) =
        (((thueMorseSign n : ℤ) : ℂ) * ((thueMorseSign n' : ℤ) : ℂ)) *
          (if ((n : ℤ) - (n' : ℤ) : ℤ) = 0 then 1 else 0) := by
      intro n' _
      rw [intervalIntegral.integral_const_mul,
        integral_exp_two_pi_int ((n : ℤ) - (n' : ℤ))]
    rw [Finset.sum_congr rfl hterm]
    have hcollapse : ∀ n' ∈ range (2 ^ m),
        (((thueMorseSign n : ℤ) : ℂ) * ((thueMorseSign n' : ℤ) : ℂ)) *
          (if ((n : ℤ) - (n' : ℤ) : ℤ) = 0 then 1 else 0) =
        (if n' = n then 1 else 0) := by
      intro n' _
      by_cases h : n' = n
      · subst h
        rw [if_pos rfl, if_pos (by omega), mul_one]
        rw [← Int.cast_mul, thueMorseSign_mul_self]
        norm_num
      · rw [if_neg h, if_neg (by omega), mul_zero]
    rw [Finset.sum_congr rfl hcollapse,
      Finset.sum_ite_eq' (range (2 ^ m)) n (fun _ => (1 : ℂ)),
      if_pos hn]
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, Finset.card_range]
  simp

end Fabius
