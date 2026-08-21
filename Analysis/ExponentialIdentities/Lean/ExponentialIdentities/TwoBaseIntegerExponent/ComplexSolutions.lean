import ExponentialIdentities.TwoBaseIntegerExponent.LeastSolution
import ExponentialIdentities.TwoBaseIntegerExponent.MultiplicativeRank
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Complexifying the exponent adds nothing

The conjecture is usually stated for a real exponent.  This module shows that the restriction
is cosmetic: on the principal branch, every *complex* `x` with `2 ^ x` and `3 ^ x` integers is
already real.

The mechanism is an incommensurability.  Writing `x = s + i t`, the modulus of `2 ^ x` is
`2 ^ s`, which reproduces the real hypothesis, while its argument is `t log 2`; integrality
forces the value to be real, hence `t log 2 ∈ π ℤ`, and likewise `t log 3 ∈ π ℤ`.  The two
gratings of admissible imaginary parts have spacings `π / log 2` and `π / log 3`, and these are
incommensurable *precisely because* `log₂ 3` is irrational.  So they meet only at `t = 0`.

Only irrationality of `log₂ 3` is used — no transcendence input — so the reduction is
unconditional and cheap, and the conjecture may be stated over `ℂ` at no mathematical cost.

The predicate is phrased through `Complex.exp` with the real logarithms, which is exactly the
principal branch: `2 ^ x = exp (x * log 2)` because `2` is a positive real.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- The two-base integrality condition for a complex exponent, on the principal branch. -/
def ComplexTwoBaseIntegralSolution (x : ℂ) : Prop :=
  Complex.exp (x * (Real.log 2 : ℂ)) ∈ Set.range ((↑) : ℤ → ℂ) ∧
    Complex.exp (x * (Real.log 3 : ℂ)) ∈ Set.range ((↑) : ℤ → ℂ)

/-- If `exp (x * c)` is an integer for a positive real `c`, the imaginary part of `x * c` is an
integer multiple of `π`. -/
private theorem exists_int_mul_pi_of_exp_mul_integer {x : ℂ} {c : ℝ}
    (h : Complex.exp (x * (c : ℂ)) ∈ Set.range ((↑) : ℤ → ℂ)) :
    ∃ a : ℤ, (a : ℝ) * Real.pi = x.im * c := by
  obtain ⟨m, hm⟩ := h
  have him : (Complex.exp (x * (c : ℂ))).im = 0 := by
    rw [← hm]
    simp
  rw [Complex.exp_im] at him
  have hmul : (x * (c : ℂ)).im = x.im * c := by simp
  rw [hmul] at him
  have hexp : Real.exp (x * (c : ℂ)).re ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hsin : Real.sin (x.im * c) = 0 := by
    rcases mul_eq_zero.mp him with h1 | h2
    · exact absurd h1 hexp
    · exact h2
  exact Real.sin_eq_zero_iff.mp hsin

/-- **Every complex solution is real.**  On the principal branch, if `2 ^ x` and `3 ^ x` are
integers for a complex `x`, then `x` is real.  Only irrationality of `log₂ 3` is used. -/
theorem im_eq_zero_of_complexTwoBaseIntegralSolution {x : ℂ}
    (h : ComplexTwoBaseIntegralSolution x) : x.im = 0 := by
  obtain ⟨a, ha⟩ := exists_int_mul_pi_of_exp_mul_integer h.1
  obtain ⟨b, hb⟩ := exists_int_mul_pi_of_exp_mul_integer h.2
  by_contra hne
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hane : (a : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at ha
    rcases mul_eq_zero.mp ha.symm with h1 | h2
    · exact hne h1
    · exact hlog2 h2
  have hcross : x.im * ((b : ℝ) * Real.log 2) = x.im * ((a : ℝ) * Real.log 3) := by
    have h1 : (b : ℝ) * ((a : ℝ) * Real.pi) = (a : ℝ) * ((b : ℝ) * Real.pi) := by ring
    rw [ha, hb] at h1
    calc x.im * ((b : ℝ) * Real.log 2) = (b : ℝ) * (x.im * Real.log 2) := by ring
      _ = (a : ℝ) * (x.im * Real.log 3) := h1
      _ = x.im * ((a : ℝ) * Real.log 3) := by ring
  have hkey : (b : ℝ) * Real.log 2 = (a : ℝ) * Real.log 3 :=
    mul_left_cancel₀ hne hcross
  have hcast : (((b : ℚ) / (a : ℚ) : ℚ) : ℝ) = (b : ℝ) / (a : ℝ) := by
    push_cast
    ring
  have hq : (((b : ℚ) / (a : ℚ) : ℚ) : ℝ) = logThreeDivLogTwo := by
    rw [hcast, logThreeDivLogTwo, div_eq_div_iff hane hlog2]
    calc (b : ℝ) * Real.log 2 = (a : ℝ) * Real.log 3 := hkey
      _ = Real.log 3 * (a : ℝ) := by ring
  exact irrational_logThreeDivLogTwo ⟨(b : ℚ) / (a : ℚ), hq⟩

/-- A complex solution restricts to a real solution at its real part. -/
theorem twoBaseIntegralSolution_re_of_complex {x : ℂ}
    (h : ComplexTwoBaseIntegralSolution x) : TwoBaseIntegralSolution x.re := by
  have him := im_eq_zero_of_complexTwoBaseIntegralSolution h
  have key : ∀ (c : ℝ), 0 < c →
      Complex.exp (x * (c : ℂ)) ∈ Set.range ((↑) : ℤ → ℂ) →
      Real.exp (x.re * c) ∈ Set.range ((↑) : ℤ → ℝ) := by
    intro c _ hc
    obtain ⟨m, hm⟩ := hc
    refine ⟨m, ?_⟩
    have hre : ((m : ℤ) : ℝ) = (Complex.exp (x * (c : ℂ))).re := by
      simpa using congrArg Complex.re hm
    rw [Complex.exp_re, Complex.mul_re, Complex.mul_im] at hre
    simpa [him] using hre
  refine ⟨?_, ?_⟩
  · have h2 := key (Real.log 2) (Real.log_pos (by norm_num)) h.1
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), mul_comm (Real.log 2) x.re]
    exact h2
  · have h3 := key (Real.log 3) (Real.log_pos (by norm_num)) h.2
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), mul_comm (Real.log 3) x.re]
    exact h3

end LeanProofs.TwoBaseIntegerExponent
