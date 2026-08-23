import IntegerPoints.KuzminLandau
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A finite Hilbert inequality

This module develops the sharp finite Hilbert inequality needed by
Graham–Kolesnik's Appendix A mean-square estimate.  Its proof uses the
sawtooth weight `1/2 - x` on `[0,1]` and finite Fourier orthogonality.
-/

open Real Finset MeasureTheory intervalIntegral

namespace LeanProofs.IntegerPoints

namespace FiniteHilbert

/-- Orthogonality of the integer Fourier characters on `[0,1]`. -/
theorem integral_e_int_mul (k : ℤ) :
    (∫ x in (0 : ℝ)..1, e ((k : ℝ) * x)) =
      if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [e]
  · rw [if_neg hk]
    set c : ℂ := (((2 * π * (k : ℝ) : ℝ) : ℂ) * Complex.I) with hc
    have hreal : (2 * π * (k : ℝ) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (Int.cast_ne_zero.mpr hk)
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (by exact_mod_cast hreal) Complex.I_ne_zero
    have hefun : (fun x : ℝ => e ((k : ℝ) * x)) =
        fun x : ℝ => Complex.exp (c * x) := by
      funext x
      rw [e, hc]
      push_cast
      congr 1
      ring
    rw [hefun, integral_exp_mul_complex hc0]
    have he1 : Complex.exp (c * (1 : ℝ)) = 1 := by
      calc
        Complex.exp (c * (1 : ℝ)) = e (k : ℝ) := by
          rw [e, hc]
          push_cast
          congr 1
          ring
        _ = 1 := KL.e_int k
    rw [he1]
    simp

/-- The nonzero Fourier coefficients of the centered sawtooth on `[0,1]`.

The sign convention here matches `e x = exp (2 π i x)`: for `k ≠ 0` the
coefficient is `i / (2 π k)`. -/
theorem integral_sawtooth_mul_e_int (k : ℤ) :
    (∫ x in (0 : ℝ)..1,
        (((1 / 2 - x : ℝ) : ℂ) * e ((k : ℝ) * x))) =
      if k = 0 then 0 else Complex.I / (2 * π * (k : ℝ)) := by
  by_cases hk : k = 0
  · subst k
    rw [if_pos rfl]
    simp only [Int.cast_zero, zero_mul]
    rw [show e 0 = 1 by simp [e]]
    simp only [mul_one]
    rw [intervalIntegral.integral_ofReal]
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id]
    rw [intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    norm_num
  · rw [if_neg hk]
    set c : ℂ := (((2 * π * (k : ℝ) : ℝ) : ℂ) * Complex.I) with hc
    have hreal : (2 * π * (k : ℝ) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (Int.cast_ne_zero.mpr hk)
    have hc0 : c ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (by exact_mod_cast hreal) Complex.I_ne_zero
    have hefun : (fun x : ℝ => e ((k : ℝ) * x)) =
        fun x : ℝ => Complex.exp (c * x) := by
      funext x
      rw [e, hc]
      push_cast
      congr 1
      ring
    have hepoint (x : ℝ) : e ((k : ℝ) * x) = Complex.exp (c * x) :=
      congrFun hefun x
    simp_rw [hepoint]
    let F : ℝ → ℂ := fun x =>
      Complex.exp (c * x) *
        ((((1 / 2 - x : ℝ) : ℂ) / c) + 1 / c ^ 2)
    have hF : ∀ x : ℝ,
        HasDerivAt F
          (((1 / 2 - x : ℝ) : ℂ) * Complex.exp (c * x)) x := by
      intro x
      have hlin : HasDerivAt (fun y : ℝ => c * y) c x := by
        simpa only [mul_one] using!
          ((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal
      have hexp : HasDerivAt (fun y : ℝ => Complex.exp (c * y))
          (Complex.exp (c * x) * c) x :=
        (Complex.hasDerivAt_exp _).comp x hlin
      have hsawReal : HasDerivAt (fun y : ℝ => 1 / 2 - y) (-1) x :=
        (hasDerivAt_id x).const_sub (1 / 2 : ℝ)
      have hsaw : HasDerivAt (fun y : ℝ => ((1 / 2 - y : ℝ) : ℂ)) (-1) x :=
        by
          convert hsawReal.ofReal_comp using 1
          norm_num
      have hinner : HasDerivAt
          (fun y : ℝ => (((1 / 2 - y : ℝ) : ℂ) / c) + 1 / c ^ 2)
          ((-1 : ℂ) / c + 0) x :=
        (hsaw.div_const c).add (hasDerivAt_const x (1 / c ^ 2))
      have hprod := hexp.mul hinner
      convert hprod using 1
      all_goals try rfl
      field_simp [hc0]
      ring
    have hint : IntervalIntegrable
        (fun x : ℝ => (((1 / 2 - x : ℝ) : ℂ) * Complex.exp (c * x)))
        volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hint]
    have he0 : Complex.exp (c * (0 : ℝ)) = 1 := by simp
    have he1 : Complex.exp (c * (1 : ℝ)) = 1 := by
      calc
        Complex.exp (c * (1 : ℝ)) = e (k : ℝ) := by
          rw [e, hc]
          push_cast
          congr 1
          ring
        _ = 1 := KL.e_int k
    change Complex.exp (c * (1 : ℝ)) *
          ((((1 / 2 - (1 : ℝ) : ℝ) : ℂ) / c) + 1 / c ^ 2) -
        Complex.exp (c * (0 : ℝ)) *
          ((((1 / 2 - (0 : ℝ) : ℝ) : ℂ) / c) + 1 / c ^ 2) = _
    rw [he0, he1]
    rw [hc]
    push_cast
    field_simp [hreal, Complex.I_ne_zero]
    rw [show Complex.I ^ 3 = -Complex.I by
      rw [pow_succ, Complex.I_sq]
      ring]
    ring

end FiniteHilbert

end LeanProofs.IntegerPoints
