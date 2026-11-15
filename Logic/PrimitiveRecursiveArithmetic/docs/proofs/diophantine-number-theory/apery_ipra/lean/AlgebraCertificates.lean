import Mathlib.Tactic

/-!
# Fixed algebraic certificates used in the manuscript

STATUS: UNCOMPILED in the authoring environment. These are ordinary Lean
metatheory proof scripts for fixed identities and small comparisons. They
do not by themselves construct object-language iPRA derivations. No axiom
or `sorry` is used. The intended environment is Lean/Mathlib v4.32.0.
-/

namespace AperyIPRA.AlgebraCertificates

def recurrenceCoefficient (n : ℚ) : ℚ :=
  (2 * n + 1) * (17 * n ^ 2 + 17 * n + 5)

def telescopingFactor (n t : ℚ) : ℚ :=
  4 * (2 * n + 1) * (-2 * t ^ 2 + t + (2 * n + 1) ^ 2)

theorem cleared_telescoper (n t : ℚ) :
    (n + 1) ^ 3 * (t - n - 1) ^ 2 * (t - n) ^ 2
      - recurrenceCoefficient n * (t - n) ^ 2 * (t + n + 1) ^ 2
      + n ^ 3 * (t + n) ^ 2 * (t + n + 1) ^ 2
    = telescopingFactor n (t + 1) * t ^ 4
      - telescopingFactor n t * (t - n) ^ 2 * (t + n + 1) ^ 2 := by
  unfold recurrenceCoefficient telescopingFactor
  ring

theorem growth_shift (u : ℚ) :
    (u + 48) ^ 3 - 45 * (u + 48) ^ 2 - 69 * (u + 48) - 27
      = u ^ 3 + 99 * u ^ 2 + 2523 * u + 3573 := by
  ring

theorem tail_numerator (t : ℚ) :
    t * (2 * t - 1) - 2 * (t - 1) ^ 2 = 3 * t - 2 := by
  ring

theorem sylvester_comparison_one : (3 : ℕ) ^ 7 < 7 ^ 4 := by norm_num
theorem sylvester_comparison_two : (3 : ℕ) ^ 10 < 2 ^ 16 := by norm_num
theorem block_decay : (8 : ℕ) ^ 6 > 2 * 7 ^ 6 := by norm_num
theorem geometric_constant : (768 : ℕ) < 1023 := by norm_num

end AperyIPRA.AlgebraCertificates
