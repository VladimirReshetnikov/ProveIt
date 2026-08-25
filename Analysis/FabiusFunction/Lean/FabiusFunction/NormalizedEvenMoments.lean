import FabiusFunction.MomentPowerSeries

/-!
# Natural normalization of the even moments

This module proves, entirely in exact arithmetic, that the division-free
natural recurrence `momentNumerator` gives the numerator normalization of the
rational moment recurrence `moment` from Proposition 1 of the paper.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

private def momentDenominator (n : ℕ) : ℕ :=
  oddDoubleFactorial (n + 1) * evenMersenneProduct n

/-- Rewrite the initial even-indexed Mersenne product as a product over
`[1, n + 1)`. -/
theorem evenMersenneProduct_eq_prod_Ico (n : ℕ) :
    evenMersenneProduct n =
      ∏ j ∈ Ico 1 (n + 1), (2 ^ (2 * j) - 1) := by
  simp [evenMersenneProduct, Finset.prod_Ico_eq_prod_range, add_comm]

/-- Split an odd double factorial at an arbitrary index. -/
theorem oddDoubleFactorial_mul_interval (a b : ℕ) (hab : a ≤ b) :
    oddDoubleFactorial a * oddFactorProduct a b = oddDoubleFactorial b := by
  simpa [oddDoubleFactorial, oddFactorProduct] using
    (Finset.prod_range_mul_prod_Ico (fun j => 2 * j + 1) hab)

/-- Split the even-indexed Mersenne product at an arbitrary index. -/
theorem evenMersenneProduct_mul_interval (k n : ℕ) (hkn : k ≤ n) :
    evenMersenneProduct k *
        (∏ j ∈ Ico (k + 1) (n + 1), (2 ^ (2 * j) - 1)) =
      evenMersenneProduct n := by
  rw [evenMersenneProduct_eq_prod_Ico, evenMersenneProduct_eq_prod_Ico]
  exact Finset.prod_Ico_consecutive (fun j => 2 ^ (2 * j) - 1)
    (by omega) (Nat.succ_le_succ hkn)

private lemma momentDenominator_mul_tail (k n : ℕ) (hkn : k ≤ n) :
    momentDenominator k *
        (oddFactorProduct (k + 1) (n + 1) *
          (∏ j ∈ Ico (k + 1) (n + 1), (2 ^ (2 * j) - 1))) =
      oddDoubleFactorial (n + 1) * evenMersenneProduct n := by
  have hodd := oddDoubleFactorial_mul_interval (k + 1) (n + 1)
    (Nat.succ_le_succ hkn)
  have hmrs := evenMersenneProduct_mul_interval k n hkn
  unfold momentDenominator
  calc
    oddDoubleFactorial (k + 1) * evenMersenneProduct k *
          (oddFactorProduct (k + 1) (n + 1) *
            ∏ j ∈ Ico (k + 1) (n + 1), (2 ^ (2 * j) - 1)) =
        (oddDoubleFactorial (k + 1) * oddFactorProduct (k + 1) (n + 1)) *
          (evenMersenneProduct k *
            ∏ j ∈ Ico (k + 1) (n + 1), (2 ^ (2 * j) - 1)) := by
              ring
    _ = oddDoubleFactorial (n + 1) * evenMersenneProduct n := by
      rw [hodd, hmrs]

private lemma momentDenominator_succ (n : ℕ) :
    momentDenominator (n + 1) =
      ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
        momentDenominator n := by
  rw [momentDenominator, oddDoubleFactorial_succ, evenMersenneProduct_succ_eq,
    momentDenominator]
  ring

private lemma momentDenominator_pos (n : ℕ) : 0 < momentDenominator n := by
  exact Nat.mul_pos (oddDoubleFactorial_pos _) (evenMersenneProduct_pos _)

/-- Split an odd double factorial at its middle factor. -/
theorem oddDoubleFactorial_mul_Icc (n : ℕ) :
    (2 * n + 1) * oddDoubleFactorial (2 * n + 1) =
      oddDoubleFactorial (n + 1) *
        ∏ j ∈ Icc n (2 * n), (2 * j + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  unfold oddDoubleFactorial
  have h := Finset.prod_range_mul_prod_Ico (fun j => 2 * j + 1)
    (show n ≤ 2 * n + 1 by omega)
  rw [← h]
  rw [Finset.prod_range_succ]
  ring

/-- Casting an even-indexed Mersenne factor from `ℕ` to `ℚ`. -/
theorem mersenneFactor_cast (j : ℕ) :
    (((2 ^ (2 * j) - 1 : ℕ) : ℚ)) = (2 : ℚ) ^ (2 * j) - 1 := by
  rw [Nat.cast_sub (show 1 ≤ 2 ^ (2 * j) by exact one_le_pow₀ (by omega))]
  norm_num

/--
The division-free natural sequence `momentNumerator` is exactly the numerator
normalization of the rational moment sequence.
-/
theorem moment_eq_momentNumerator_div (n : ℕ) :
    moment n =
      (momentNumerator n : ℚ) /
        ((oddDoubleFactorial (n + 1) * evenMersenneProduct n : ℕ) : ℚ) := by
  change moment n = (momentNumerator n : ℚ) / (momentDenominator n : ℚ)
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => norm_num [moment, momentNumerator, momentDenominator,
          oddDoubleFactorial, evenMersenneProduct]
      | succ n =>
          rw [moment_succ, momentNumerator_succ]
          rw [Nat.cast_sum, Finset.sum_div, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k.val k.isLt]
          push_cast
          let tail : ℕ :=
            oddFactorProduct (k.val + 1) (n + 1) *
              ∏ j ∈ Ico (k.val + 1) (n + 1), (2 ^ (2 * j) - 1)
          have htail : momentDenominator k.val * tail = momentDenominator n := by
            exact momentDenominator_mul_tail k.val n
              (Nat.le_of_lt_succ k.isLt)
          have hdenNat :
              ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
                    momentDenominator k.val * tail =
                momentDenominator (n + 1) := by
            calc
              ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
                    momentDenominator k.val * tail =
                  ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
                    (momentDenominator k.val * tail) := by ring
              _ = ((2 * (n + 1) + 1) * (2 ^ (2 * (n + 1)) - 1)) *
                    momentDenominator n := by rw [htail]
              _ = momentDenominator (n + 1) := (momentDenominator_succ n).symm
          have hp : 1 ≤ 2 ^ (2 * (n + 1)) :=
            (Nat.one_lt_pow (by omega) (by omega)).le
          have hdenRat := congrArg (fun z : ℕ => (z : ℚ)) hdenNat
          push_cast [Nat.cast_sub hp] at hdenRat
          have hDk : ((momentDenominator k.val : ℕ) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (momentDenominator_pos k.val))
          have hDs : ((momentDenominator (n + 1) : ℕ) : ℚ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (momentDenominator_pos (n + 1)))
          have hA : (2 * (n : ℚ) + 3) ≠ 0 := by positivity
          have hB : (2 : ℚ) ^ (2 * (n + 1)) - 1 ≠ 0 := by
            exact sub_ne_zero.mpr (ne_of_gt
              (one_lt_pow₀ (a := (2 : ℚ)) (by norm_num) (by omega)))
          have htailCast :
              (tail : ℚ) =
                (oddFactorProduct (k.val + 1) (n + 1) : ℚ) *
                  ∏ j ∈ Ico (k.val + 1) (n + 1), ((2 ^ (2 * j) - 1 : ℕ) : ℚ) := by
            simp [tail]
          have hnum :
              (momentNumerator k.val : ℚ) *
                    ((2 * (n + 1) + 1).choose (2 * k.val) : ℚ) *
                    (oddFactorProduct (k.val + 1) (n + 1) : ℚ) *
                    ∏ j ∈ Ico (k.val + 1) (n + 1),
                      ((2 ^ (2 * j) - 1 : ℕ) : ℚ) =
                (momentNumerator k.val : ℚ) *
                  ((2 * (n + 1) + 1).choose (2 * k.val) : ℚ) *
                  (tail : ℚ) := by
            rw [htailCast]
            ring
          rw [hnum]
          field_simp [hDk, hDs, hA, hB]
          rw [← hdenRat]
          ring

/-- The reduced denominator of `moment n` divides its natural normalization.
This packages the exact quotient formula in a form convenient for subsequent
denominator arguments. -/
theorem moment_den_dvd_normalization (n : ℕ) :
    (moment n).den ∣
      oddDoubleFactorial (n + 1) * evenMersenneProduct n := by
  rw [moment_eq_momentNumerator_div]
  exact rat_den_dvd_nat_div _ _

end Fabius
