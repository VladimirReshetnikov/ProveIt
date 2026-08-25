import FabiusFunction.Arithmetic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Natural normalization of the half moments

This module proves that the executable rational recurrence for `halfMoment`
agrees with the division-free recurrence for `halfMomentNumerator`.  Keeping
the proof in the arithmetic layer makes the result independent of the
analytic construction of the Fabius function.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- Rewrite the initial Mersenne product as a product over the natural interval
`[1, n + 1)`. -/
theorem mersenneProduct_eq_interval (n : ℕ) :
    mersenneProduct n = mersenneIntervalProduct 1 (n + 1) := by
  rw [mersenneProduct, mersenneIntervalProduct,
    Finset.prod_Ico_eq_prod_range]
  apply Finset.prod_congr rfl
  intro k hk
  congr 2
  omega

/-- Complete `(k + 1)!` to `(n + 1)!` by multiplying by the intervening
natural factors. -/
theorem factorial_mul_interval (n k : ℕ) (hk : k ≤ n) :
    (k + 1).factorial * (∏ j ∈ Ico (k + 2) (n + 2), j) =
      (n + 1).factorial := by
  rw [← Finset.prod_Ico_id_eq_factorial,
    ← Finset.prod_Ico_id_eq_factorial]
  exact Finset.prod_Ico_consecutive id (by omega) (by omega)

/-- Complete the Mersenne product through `k` with the factors through `n`. -/
theorem mersenneProduct_mul_interval (n k : ℕ) (hk : k ≤ n) :
    mersenneProduct k * mersenneIntervalProduct (k + 1) (n + 1) =
      mersenneProduct n := by
  rw [mersenneProduct_eq_interval, mersenneProduct_eq_interval,
    mersenneIntervalProduct, mersenneIntervalProduct]
  exact Finset.prod_Ico_consecutive (fun j => 2 ^ j - 1)
    (by omega) (by omega)

/--
The division-free natural sequence `halfMomentNumerator` is the numerator
normalization of the rational half-moment sequence.
-/
theorem halfMoment_eq_halfMomentNumerator (n : ℕ) :
    halfMoment n =
      (halfMomentNumerator n : ℚ) /
        (((n + 1).factorial * mersenneProduct n : ℕ) : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [mersenneProduct, halfMomentNumerator]
      | succ n =>
          rw [halfMoment_succ]
          have hcommon :
              (∑ k : Fin (n + 1),
                (Nat.choose (n + 2) k.val : ℚ) * halfMoment k.val) =
              (halfMomentNumerator (n + 1) : ℚ) /
                (((n + 1).factorial * mersenneProduct n : ℕ) : ℚ) := by
            rw [halfMomentNumerator_succ]
            push_cast
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro k hkfin
            rw [ih k.val (by omega)]
            have hk : k.val ≤ n := by omega
            have hfac := factorial_mul_interval n k.val hk
            have hmer := mersenneProduct_mul_interval n k.val hk
            have hkmerpos : 0 < mersenneProduct k.val := mersenneProduct_pos _
            have hcommonmerpos : 0 < mersenneProduct n := mersenneProduct_pos _
            field_simp
            have hnat :
                Nat.choose (n + 2) k.val * halfMomentNumerator k.val *
                      ((n + 1).factorial * mersenneProduct n) =
                  (halfMomentNumerator k.val * Nat.choose (n + 2) k.val *
                      (∏ j ∈ Ico (k.val + 2) (n + 2), j) *
                      mersenneIntervalProduct (k.val + 1) (n + 1)) *
                    ((k.val + 1).factorial * mersenneProduct k.val) := by
              rw [← hfac, ← hmer]
              ring
            push_cast
            convert congrArg (fun z : ℕ => (z : ℚ)) hnat using 1 <;>
              push_cast <;> ring
          rw [hcommon, mersenneProduct_succ_eq]
          have hfac : (n + 2).factorial = (n + 2) * (n + 1).factorial := by
            rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ]
          have hpowNat : 1 ≤ 2 ^ (n + 1) := by
            have : 0 < 2 ^ (n + 1) := pow_pos (by omega) _
            omega
          have hcastNew : (((2 ^ (n + 1) - 1 : ℕ) : ℚ)) =
              (2 : ℚ) ^ (n + 1) - 1 := by
            rw [Nat.cast_sub hpowNat]
            norm_num
          rw [hfac]
          push_cast
          rw [hcastNew, pow_succ]
          have hmpos : (0 : ℚ) < mersenneProduct n := by
            exact_mod_cast mersenneProduct_pos n
          have hnewpos : (0 : ℚ) < (2 : ℚ) ^ n * 2 - 1 := by
            have : (1 : ℚ) ≤ (2 : ℚ) ^ n := one_le_pow₀ (by norm_num)
            nlinarith
          field_simp [ne_of_gt hmpos, ne_of_gt hnewpos]

/-- The reduced denominator of a half moment divides the displayed natural
normalization from its division-free recurrence. -/
theorem halfMoment_den_dvd_normalization (n : ℕ) :
    (halfMoment n).den ∣ (n + 1).factorial * mersenneProduct n := by
  rw [halfMoment_eq_halfMomentNumerator]
  exact rat_den_dvd_nat_div _ _

end Fabius
