import FabiusFunction.DyadicAnalytic
import FabiusFunction.AnalyticMoments

/-!
# Named rational specializations of the dyadic calculus

The umbrella gap register's *Concrete rational values* candidate lists
four exact rationals with no named theorems: the first nontrivial even
moment `c₁ = ∫ x²·up = 1/9` and the bounded values `F(1/4) = 5/72`,
`F(1/8) = 1/288`, `F(3/8) = 73/288`.  This module names them, each in
two forms as the register's obligation asks: the executable reduction
(`moment`, `fabiusDyadic` — closed rational arithmetic normalized by
`norm_num`) and the analytic bridge (the full-line and interval moment
integrals; `fabiusReal` at the dyadic argument, for every bounded
Fabius function).

* `moment_one`, `integral_sq_mul_rvachev_eq_one_ninth`,
  `intervalIntegral_sq_mul_rvachev_eq_one_ninth` — `c₁ = 1/9`.
* `fabiusDyadic_two_one` / `fabiusReal_one_quarter` — `F(1/4) = 5/72`.
* `fabiusDyadic_three_one` / `fabiusReal_one_eighth` — `F(1/8) = 1/288`.
* `fabiusDyadic_three_three` / `fabiusReal_three_eighths` —
  `F(3/8) = 73/288`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

private lemma thueMorseSign_zero' : thueMorseSign 0 = 1 := by
  norm_num [thueMorseSign, binaryWeight, Nat.digits_zero]

private lemma thueMorseSign_one' : thueMorseSign 1 = -1 := by
  simpa [thueMorseSign_zero'] using thueMorseSign_two_mul_add_one 0

private lemma thueMorseSign_two' : thueMorseSign 2 = -1 := by
  simpa [thueMorseSign_one'] using thueMorseSign_two_mul 1

/-- **`μ₁ = 1/9`**: the first nontrivial value of the executable
rational even-moment sequence, from its defining recurrence. -/
theorem moment_one : moment 1 = 1 / 9 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, moment_succ]
  norm_num [Fin.sum_univ_one, moment_zero]

/-- **`c₁ = ∫ x²·up(x) dx = 1/9`**, over the whole line. -/
theorem integral_sq_mul_rvachev_eq_one_ninth
    (F : BoundedFabius) (hF : IsFabius F) :
    (∫ x : ℝ, x ^ 2 * rvachevUp F x) = 1 / 9 := by
  have h := integral_even_pow_mul_rvachev_eq_moment F hF 1
  rw [show 2 * 1 = 2 from rfl] at h
  rw [h, moment_one]
  norm_num

/-- **`c₁ = ∫_{-1}^{1} x²·up(x) dx = 1/9`**, in the register's interval
form (the support of `up` is inside `[-1, 1]`). -/
theorem intervalIntegral_sq_mul_rvachev_eq_one_ninth
    (F : BoundedFabius) (hF : IsFabius F) :
    (∫ x in (-1 : ℝ)..1, x ^ 2 * rvachevUp F x) = 1 / 9 := by
  have hsupp : ∀ x ∉ Set.Ioc (-1 : ℝ) 1, x ^ 2 * rvachevUp F x = 0 := by
    intro x hx
    rw [Set.mem_Ioc, not_and_or] at hx
    rcases hx with h | h
    · rw [rvachevUp_eq_zero_of_le_neg_one F hF (not_lt.mp h), mul_zero]
    · rw [rvachevUp_eq_zero_of_one_le F hF (not_le.mp h).le, mul_zero]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
    integral_sq_mul_rvachev_eq_one_ninth F hF]

/-- The executable reduction `F(1/4) = 5/72`: the closed dyadic formula
at scale `2`, numerator `1`. -/
theorem fabiusDyadic_two_one : fabiusDyadic 2 1 = 5 / 72 := by
  show (2 : ℚ) ^ (-(Nat.choose 3 2 : ℤ)) / (Nat.factorial 2 : ℚ) *
      ∑ h : Fin 1, (thueMorseSign h.val : ℚ) *
        ∑ k : Fin 2, (Nat.choose 2 (2 * k.val) : ℚ) *
          ((2 : ℚ) * 1 - 2 * h.val - 1) ^ (2 - 2 * k.val) * moment k.val =
    5 / 72
  rw [Fin.sum_univ_one, Fin.sum_univ_two]
  norm_num [thueMorseSign_zero', moment_zero, moment_one, Nat.factorial, Nat.choose]

/-- The executable reduction `F(1/8) = 1/288`: the closed dyadic
formula at scale `3`, numerator `1`. -/
theorem fabiusDyadic_three_one : fabiusDyadic 3 1 = 1 / 288 := by
  show (2 : ℚ) ^ (-(Nat.choose 4 2 : ℤ)) / (Nat.factorial 3 : ℚ) *
      ∑ h : Fin 1, (thueMorseSign h.val : ℚ) *
        ∑ k : Fin 2, (Nat.choose 3 (2 * k.val) : ℚ) *
          ((2 : ℚ) * 1 - 2 * h.val - 1) ^ (3 - 2 * k.val) * moment k.val =
    1 / 288
  rw [Fin.sum_univ_one, Fin.sum_univ_two]
  norm_num [thueMorseSign_zero', moment_zero, moment_one, Nat.factorial, Nat.choose]

/-- The executable reduction `F(3/8) = 73/288`: the closed dyadic
formula at scale `3`, numerator `3`. -/
theorem fabiusDyadic_three_three : fabiusDyadic 3 3 = 73 / 288 := by
  show (2 : ℚ) ^ (-(Nat.choose 4 2 : ℤ)) / (Nat.factorial 3 : ℚ) *
      ∑ h : Fin 3, (thueMorseSign h.val : ℚ) *
        ∑ k : Fin 2, (Nat.choose 3 (2 * k.val) : ℚ) *
          ((2 : ℚ) * 3 - 2 * h.val - 1) ^ (3 - 2 * k.val) * moment k.val =
    73 / 288
  rw [Fin.sum_univ_three]
  simp only [Fin.sum_univ_two]
  norm_num [thueMorseSign_zero', thueMorseSign_one', thueMorseSign_two',
    moment_zero, moment_one, Nat.factorial, Nat.choose]

/-- **`F(1/4) = 5/72`** for every bounded Fabius function: the
executable value bridged to the analytic function. -/
theorem fabiusReal_one_quarter (F : BoundedFabius) (hF : IsFabius F) :
    fabiusReal F (1 / 4) = 5 / 72 := by
  have h := fabiusDyadic_cast F hF 2 1 (by norm_num)
  rw [fabiusDyadic_two_one,
    show ((1 : ℕ) : ℝ) / (2 : ℝ) ^ 2 = 1 / 4 by norm_num] at h
  rw [← h]
  norm_num

/-- **`F(1/8) = 1/288`** for every bounded Fabius function. -/
theorem fabiusReal_one_eighth (F : BoundedFabius) (hF : IsFabius F) :
    fabiusReal F (1 / 8) = 1 / 288 := by
  have h := fabiusDyadic_cast F hF 3 1 (by norm_num)
  rw [fabiusDyadic_three_one,
    show ((1 : ℕ) : ℝ) / (2 : ℝ) ^ 3 = 1 / 8 by norm_num] at h
  rw [← h]
  norm_num

/-- **`F(3/8) = 73/288`** for every bounded Fabius function. -/
theorem fabiusReal_three_eighths (F : BoundedFabius) (hF : IsFabius F) :
    fabiusReal F (3 / 8) = 73 / 288 := by
  have h := fabiusDyadic_cast F hF 3 3 (by norm_num)
  rw [fabiusDyadic_three_three,
    show ((3 : ℕ) : ℝ) / (2 : ℝ) ^ 3 = 3 / 8 by norm_num] at h
  rw [← h]
  norm_num

end Fabius
