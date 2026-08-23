import IntegerPoints.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.Interval

/-!
# Graham--Kolesnik section 3.3: size of the square-root dual range

The B-process applied to the square-root phase produces the integer interval
`[ceil (H / sqrt 2), H]`.  This file records the elementary fact that the
interval contains at least `H / 4` integers.  The deliberately comfortable
constant avoids introducing any decimal approximation to `sqrt 2`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-- The square-root B-process dual interval contains at least `H / 4`
integers. -/
theorem dualRange_card_ge_quarter (H : ℕ) (hH : 0 < H) :
    (H : ℝ) / 4 ≤
      ((Finset.Icc ⌈(H : ℝ) / Real.sqrt 2⌉ (H : ℤ)).card : ℝ) := by
  set A : ℤ := ⌈(H : ℝ) / Real.sqrt 2⌉ with hA
  have hHR : 0 ≤ (H : ℝ) := (Nat.cast_pos.2 hH).le
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt 2 := Real.one_lt_sqrt_two.le
  have hquot : (H : ℝ) / Real.sqrt 2 ≤ (H : ℝ) := by
    apply (div_le_iff₀ hsqrt0).2
    calc
      (H : ℝ) = (H : ℝ) * 1 := by ring
      _ ≤ (H : ℝ) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left hsqrt1 hHR
  have hAH : A ≤ (H : ℤ) := by
    rw [hA, Int.ceil_le]
    exact hquot
  have hcard :
      ((Finset.Icc A (H : ℤ)).card : ℝ) =
        (((H : ℤ) + 1 - A : ℤ) : ℝ) := by
    exact_mod_cast
      (Int.card_Icc_of_le A (H : ℤ) (hAH.trans (by omega)))
  have hceil :
      (A : ℝ) < (H : ℝ) / Real.sqrt 2 + 1 := by
    rw [hA]
    exact Int.ceil_lt_add_one _
  have hlower :
      (H : ℝ) - (H : ℝ) / Real.sqrt 2 ≤
        ((Finset.Icc A (H : ℤ)).card : ℝ) := by
    rw [hcard]
    push_cast
    linarith
  have hsqrtLower : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hinvUpper : 1 / Real.sqrt 2 ≤ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ hsqrt0).2
    calc
      (1 : ℝ) = (3 / 4 : ℝ) * (4 / 3 : ℝ) := by norm_num
      _ ≤ (3 / 4 : ℝ) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left hsqrtLower (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hinvUpper hHR
  change (H : ℝ) / 4 ≤ ((Finset.Icc A (H : ℤ)).card : ℝ)
  calc
    (H : ℝ) / 4 = (H : ℝ) - (H : ℝ) * (3 / 4 : ℝ) := by ring
    _ ≤ (H : ℝ) - (H : ℝ) * (1 / Real.sqrt 2) :=
      sub_le_sub_left hmul _
    _ = (H : ℝ) - (H : ℝ) / Real.sqrt 2 := by
      simp only [div_eq_mul_inv, one_mul]
    _ ≤ ((Finset.Icc A (H : ℤ)).card : ℝ) := hlower

end GKSec33

end LeanProofs.IntegerPoints
