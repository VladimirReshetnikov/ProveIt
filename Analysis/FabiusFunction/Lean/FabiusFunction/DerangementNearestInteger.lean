import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Algebra.Order.Round

/-!
# The nearest-integer property of the derangement numbers

The transseries volume's `p8:cor:nearest-integer` states that for every `n ≥ 0`

`D_n = n!/e + (-1)^n C(n)`,   `C(x) = ∫_0^1 e^{t-1} t^x dt`,

that `0 < C(x) < 1/(x+1)` for `x > -1`, and hence that for `n ≥ 1` the
correction is smaller than `1/2` in absolute value, so `D_n` is the nearest
integer to `n!/e`.

This module formalizes that, for integer `x = n`.  Mathlib knows the
derangement numbers (`numDerangements`) and that `D_n / n! → e^{-1}`
(`numDerangements_tendsto_inv_e`), but it does not have the nearest-integer
property, nor any quantitative form of the limit.

The volume derives the identity from the branch-splitting theorem
`p8:thm:branch-splitting`, i.e. from continuing the incomplete gamma function
around `0`.  That is not needed.  Both sides satisfy the *same* first-order
recursion — `C(n+1) = 1 - (n+1) C(n)`, which is one application of the
fundamental theorem of calculus to `t ↦ e^{t-1} t^{n+1}`, and
`D_{n+1} = (n+1) D_n - (-1)^n`, which is Mathlib's `numDerangements_succ` —
and they agree at `n = 0`.  So the identity is an induction, and the whole
result needs no complex analysis at all.

## Main results

* `Fabius.subfactorialDefect`: the volume's `C(n)`, as an interval integral.
* `Fabius.subfactorialDefect_succ`: `C(n+1) + (n+1) C(n) = 1`.
* `Fabius.numDerangements_sub_eq`: `D_n - n! e^{-1} = (-1)^n C(n)`, the identity
  of `p8:cor:nearest-integer`.
* `Fabius.subfactorialDefect_pos` and `Fabius.subfactorialDefect_lt`:
  `0 < C(n) < 1/(n+1)`, the volume's `p8:eq:C-bound` at integer argument.
* `Fabius.abs_numDerangements_sub_lt_half`: `|D_n - n! e^{-1}| < 1/2` for
  `n ≥ 1`.
* `Fabius.round_factorial_mul_exp_neg_one`: `round (n! e^{-1}) = D_n` for
  `n ≥ 1` — the nearest-integer property itself.

Not formalized here: the bound `0 < C(x) < 1/(x+1)` at real `x > -1` (which
needs `rpow` in place of the monoid power), and the branch-splitting theorem
`p8:thm:branch-splitting` that produces the whole family `S_κ`.
-/

set_option autoImplicit false

namespace Fabius

open MeasureTheory Set intervalIntegral

/-- The volume's `C(n) = ∫_0^1 e^{t-1} t^n dt`: the defect between the
derangement number `D_n` and `n!/e`, up to the sign `(-1)^n`. -/
noncomputable def subfactorialDefect (n : ℕ) : ℝ :=
  ∫ t in (0:ℝ)..1, Real.exp (t - 1) * t ^ n

private theorem continuous_defectIntegrand (n : ℕ) :
    Continuous fun t : ℝ => Real.exp (t - 1) * t ^ n :=
  (Real.continuous_exp.comp (continuous_id.sub continuous_const)).mul (continuous_pow n)

private theorem intervalIntegrable_defectIntegrand (n : ℕ) :
    IntervalIntegrable (fun t : ℝ => Real.exp (t - 1) * t ^ n) volume 0 1 :=
  (continuous_defectIntegrand n).intervalIntegrable _ _

/-- At index zero the subfactorial defect is `1 - exp (-1)`. -/
theorem subfactorialDefect_zero : subfactorialDefect 0 = 1 - Real.exp (-1) := by
  have hd : ∀ x ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.exp (t - 1)) (Real.exp (x - 1) * x ^ 0) x := by
    intro x _
    simpa using ((hasDerivAt_id x).sub_const 1).exp
  have key := integral_eq_sub_of_hasDerivAt hd (intervalIntegrable_defectIntegrand 0)
  rw [subfactorialDefect, key]
  norm_num

/-- The recursion `C(n+1) + (n+1) C(n) = 1`.  This is the fundamental theorem
of calculus applied to `t ↦ e^{t-1} t^{n+1}`, whose derivative is the sum of the
two integrands. -/
theorem subfactorialDefect_succ (n : ℕ) :
    subfactorialDefect (n + 1) + ((n : ℝ) + 1) * subfactorialDefect n = 1 := by
  have hd : ∀ x ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.exp (t - 1) * t ^ (n + 1))
        (Real.exp (x - 1) * x ^ (n + 1) + ((n : ℝ) + 1) * (Real.exp (x - 1) * x ^ n)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (t - 1)) (Real.exp (x - 1)) x := by
      simpa using ((hasDerivAt_id x).sub_const 1).exp
    have h2 : HasDerivAt (fun t : ℝ => t ^ (n + 1)) (((n : ℝ) + 1) * x ^ n) x := by
      simpa using hasDerivAt_pow (n + 1) x
    rw [show Real.exp (x - 1) * x ^ (n + 1) + ((n : ℝ) + 1) * (Real.exp (x - 1) * x ^ n)
        = Real.exp (x - 1) * x ^ (n + 1) + Real.exp (x - 1) * (((n : ℝ) + 1) * x ^ n) from by
      ring]
    exact h1.mul h2
  have hint : IntervalIntegrable
      (fun x : ℝ => Real.exp (x - 1) * x ^ (n + 1) + ((n : ℝ) + 1) * (Real.exp (x - 1) * x ^ n))
      volume 0 1 :=
    (intervalIntegrable_defectIntegrand (n + 1)).add
      ((intervalIntegrable_defectIntegrand n).const_mul _)
  have key := integral_eq_sub_of_hasDerivAt hd hint
  rw [integral_add (intervalIntegrable_defectIntegrand (n + 1))
    ((intervalIntegrable_defectIntegrand n).const_mul _),
    intervalIntegral.integral_const_mul] at key
  rw [subfactorialDefect, subfactorialDefect, key]
  rw [zero_pow (Nat.succ_ne_zero n)]
  norm_num

/-- `0 < C(n)`. -/
theorem subfactorialDefect_pos (n : ℕ) : 0 < subfactorialDefect n := by
  refine intervalIntegral_pos_of_pos_on (intervalIntegrable_defectIntegrand n) ?_ (by norm_num)
  intro x hx
  have hx0 : 0 < x := hx.1
  positivity

/-- `C(n) < 1/(n+1)`: the volume's `p8:eq:C-bound` at integer argument.  The
comparison is against `∫_0^1 t^n = 1/(n+1)`, strict because `e^{t-1} < 1` off
the right endpoint. -/
theorem subfactorialDefect_lt (n : ℕ) : subfactorialDefect n < 1 / ((n : ℝ) + 1) := by
  have hlt : subfactorialDefect n < ∫ x in (0:ℝ)..1, x ^ n := by
    refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
      (continuous_defectIntegrand n).continuousOn (continuous_pow n).continuousOn ?_ ?_
    · intro x hx
      have h1 : Real.exp (x - 1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.2])
      have h2 : (0:ℝ) ≤ x ^ n := pow_nonneg (le_of_lt hx.1) n
      nlinarith
    · refine ⟨1 / 2, by norm_num, ?_⟩
      have h1 : Real.exp ((1:ℝ) / 2 - 1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      have h2 : (0:ℝ) < ((1:ℝ) / 2) ^ n := by positivity
      nlinarith
  rw [integral_pow] at hlt
  rw [zero_pow (Nat.succ_ne_zero n)] at hlt
  simpa using hlt

/-- The identity of `p8:cor:nearest-integer`: `D_n - n! e^{-1} = (-1)^n C(n)`.
Both sides obey the same first-order recursion and agree at `n = 0`. -/
theorem numDerangements_sub_eq (n : ℕ) :
    (numDerangements n : ℝ) - (Nat.factorial n : ℝ) * Real.exp (-1)
      = (-1) ^ n * subfactorialDefect n := by
  induction n with
  | zero =>
      rw [subfactorialDefect_zero]
      norm_num
  | succ n ih =>
      have hD : (numDerangements (n + 1) : ℝ)
          = ((n : ℝ) + 1) * (numDerangements n : ℝ) - (-1) ^ n := by
        have h := numDerangements_succ n
        exact_mod_cast h
      have hfac : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hC : subfactorialDefect (n + 1) = 1 - ((n : ℝ) + 1) * subfactorialDefect n := by
        have h := subfactorialDefect_succ n
        linarith
      rw [hD, hfac, hC]
      linear_combination ((n : ℝ) + 1) * ih

/-- For `n ≥ 1` the correction is smaller than `1/2`. -/
theorem abs_numDerangements_sub_lt_half {n : ℕ} (hn : 1 ≤ n) :
    |(numDerangements n : ℝ) - (Nat.factorial n : ℝ) * Real.exp (-1)| < 1 / 2 := by
  rw [numDerangements_sub_eq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (subfactorialDefect_pos n)]
  have h1 : subfactorialDefect n < 1 / ((n : ℝ) + 1) := subfactorialDefect_lt n
  have h2 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  linarith

/-- The nearest-integer property: for `n ≥ 1`, the derangement number `D_n` is
the nearest integer to `n!/e`. -/
theorem round_factorial_mul_exp_neg_one {n : ℕ} (hn : 1 ≤ n) :
    round ((Nat.factorial n : ℝ) * Real.exp (-1)) = (numDerangements n : ℤ) := by
  have h := abs_numDerangements_sub_lt_half hn
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  rw [round_eq, Int.floor_eq_iff]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

end Fabius
