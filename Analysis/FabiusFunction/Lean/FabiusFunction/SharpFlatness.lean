import FabiusFunction.Monotonicity
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Flatness at the origin with the factorial constant

`FabiusFunction.EffectiveFlatness` derives `F(x) ≤ 2^C(n+1,2) x^n` from the
mean value theorem.  Replacing the mean value theorem by the fundamental
theorem of calculus recovers the factorial that the pointwise estimate throws
away: integrating

`F(x) = ∫₀ˣ 2 F(2t) dt`

against the inductive hypothesis `F(y) ≤ a_n yⁿ` gives
`a_{n+1} = 2^{n+1} a_n / (n+1)` instead of `a_{n+1} = 2^{n+1} a_n`, so

`F(x) ≤ 2^C(n+1,2) / n! · xⁿ`   whenever `0 ≤ x` and `2ⁿ x ≤ 1`.

At `x = 2^(-n)` the exact value is `2^(-C(n,2)) d_n / n!` with `d_n` the half
moment of `FabiusFunction.Arithmetic`, so the remaining overshoot is exactly
`1 / d_n`; the factorial removed here was the whole gap between the two
elementary derivations.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- The fundamental theorem of calculus for the bounded Fabius function,
using the global differential equation `F'(t) = 2 up(2t - 1)`. -/
theorem integral_deriv_fabiusReal (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    (∫ t in (0 : ℝ)..x, 2 * rvachevUp F (2 * t - 1)) = fabiusReal F x := by
  have hcont : Continuous (fun t : ℝ => 2 * rvachevUp F (2 * t - 1)) :=
    continuous_const.mul
      ((rvachev_contDiff F hF).continuous.comp
        ((continuous_const.mul continuous_id).sub continuous_const))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fabiusReal F) (f' := fun t : ℝ => 2 * rvachevUp F (2 * t - 1))
    (fun t _ => fabius_hasDerivAt F hF t) hcont.intervalIntegrable
  rw [h, hF.zero_of_nonpos 0 le_rfl, sub_zero]

/-- On the first half of the unit interval the integrand is `2 F(2t)`. -/
theorem fabiusReal_eq_integral (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    fabiusReal F x = ∫ t in (0 : ℝ)..x, 2 * fabiusReal F (2 * t) := by
  rw [← integral_deriv_fabiusReal F hF x]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hx0] at ht
  have ht2 : 2 * t - 1 ≤ 0 := by
    have := ht.2
    linarith
  simp only
  rw [rvachevUp_of_nonpos F ht2, show 2 * t - 1 + 1 = 2 * t by ring]

/--
Effective flatness of the Fabius function at the origin, with the factorial:

`F(x) ≤ 2^C(n+1,2) / n! · xⁿ`   whenever `0 ≤ x` and `2ⁿ x ≤ 1`.
-/
theorem fabiusReal_le_two_pow_div_factorial_mul_pow (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx : (2 : ℝ) ^ n * x ≤ 1) :
    fabiusReal F x ≤ 2 ^ (n + 1).choose 2 / (n.factorial : ℝ) * x ^ n := by
  induction n generalizing x with
  | zero => simpa using fabiusReal_le_one F x
  | succ n ih =>
      have hfacpos : (0 : ℝ) < (n.factorial : ℝ) :=
        Nat.cast_pos.mpr n.factorial_pos
      have hps : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hpow2 : (2 : ℝ) ≤ 2 ^ (n + 1) := by
        rw [hps]; nlinarith
      have hhalf : x ≤ 1 / 2 := by nlinarith
      set a : ℝ := 2 ^ (n + 1).choose 2 / (n.factorial : ℝ) with ha
      have hapos : (0 : ℝ) ≤ a := by
        rw [ha]; positivity
      set D : ℝ := 2 ^ (n + 1) * a with hD
      have hDpos : (0 : ℝ) ≤ D := by
        rw [hD]; positivity
      -- the integrand is dominated by `D tⁿ` on `[0, x]`
      have hdom : ∀ t ∈ Icc (0 : ℝ) x, 2 * fabiusReal F (2 * t) ≤ D * t ^ n := by
        intro t ht
        have ht0 : (0 : ℝ) ≤ t := ht.1
        have htx : t ≤ x := ht.2
        have harg : (2 : ℝ) ^ n * (2 * t) ≤ 1 := by
          have hxx : (2 : ℝ) ^ n * 2 * t ≤ 2 ^ n * 2 * x := by nlinarith
          calc (2 : ℝ) ^ n * (2 * t) = 2 ^ n * 2 * t := by ring
            _ ≤ 2 ^ n * 2 * x := hxx
            _ = 2 ^ (n + 1) * x := by rw [hps]
            _ ≤ 1 := hx
        have hIH := ih (by linarith : (0 : ℝ) ≤ 2 * t) harg
        have hpow : (2 * t) ^ n = 2 ^ n * t ^ n := by rw [mul_pow]
        rw [hpow] at hIH
        have : 2 * fabiusReal F (2 * t) ≤ 2 * (a * (2 ^ n * t ^ n)) := by
          nlinarith [hIH]
        calc 2 * fabiusReal F (2 * t) ≤ 2 * (a * (2 ^ n * t ^ n)) := this
          _ = D * t ^ n := by rw [hD, hps]; ring
      -- integrate the domination
      have hcontL : Continuous (fun t : ℝ => 2 * fabiusReal F (2 * t)) :=
        continuous_const.mul
          (hF.contDiff.continuous.comp (continuous_const.mul continuous_id))
      have hcontR : Continuous (fun t : ℝ => D * t ^ n) :=
        continuous_const.mul (continuous_pow n)
      have hmono :
          (∫ t in (0 : ℝ)..x, 2 * fabiusReal F (2 * t)) ≤
            ∫ t in (0 : ℝ)..x, D * t ^ n :=
        intervalIntegral.integral_mono_on hx0 hcontL.intervalIntegrable
          hcontR.intervalIntegrable hdom
      have hright : (∫ t in (0 : ℝ)..x, D * t ^ n) =
          D * (x ^ (n + 1) / (n + 1)) := by
        rw [intervalIntegral.integral_const_mul, integral_pow]
        have hzero : (0 : ℝ) ^ (n + 1) = 0 := by
          simp
        rw [hzero, sub_zero]
        push_cast
        ring
      rw [fabiusReal_eq_integral F hF hx0 hhalf]
      refine hmono.trans ?_
      rw [hright]
      -- rewrite the constant into the claimed form
      have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
        rw [show n + 2 = (n + 1) + 1 by omega, show 2 = 1 + 1 by omega,
          Nat.choose_succ_succ]
        simp [Nat.choose_one_right, add_comm]
      have hfac : (((n + 1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      rw [hD, ha, show n + 1 + 1 = n + 2 by omega, hchoose, hfac, pow_add]
      field_simp
      ring

end Fabius
