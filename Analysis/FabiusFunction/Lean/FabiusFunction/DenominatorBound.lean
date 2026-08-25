import FabiusFunction.NormalizedEvenMoments
import FabiusFunction.TwoAdic

/-!
# A common denominator for dyadic Fabius values

This file proves the exact-arithmetic content of Theorem 13 in Arias de
Reyna's *Arithmetic of the Fabius function*.  The moments occurring in the
closed dyadic formula are first put over one common denominator.  After the
factorial and power-of-two normalizations cancel, the scaled value is an
integer.  The nonnegative exact representation of `rvachevDyadic` turns its
absolute value into a natural number and yields the LCM denominator bound.
-/

set_option autoImplicit false

open scoped BigOperators Interval
open Finset

namespace Fabius

/-- The numerator obtained by putting `moment k` over the common moment
denominator at level `m`.  Its intended use has the side condition `k ≤ m`. -/
def commonMomentNumerator (m k : ℕ) : ℕ :=
  momentNumerator k * oddFactorProduct (k + 1) (m + 1) *
    (∏ j ∈ Ico (k + 1) (m + 1), (2 ^ (2 * j) - 1))

/-- Every moment through index `m` becomes natural after multiplication by
the level-`m` common moment denominator. -/
theorem moment_mul_common_denominator (m k : ℕ) (hk : k ≤ m) :
    moment k *
        ((oddDoubleFactorial (m + 1) * evenMersenneProduct m : ℕ) : ℚ) =
      (commonMomentNumerator m k : ℚ) := by
  let tail : ℕ := oddFactorProduct (k + 1) (m + 1) *
    (∏ j ∈ Ico (k + 1) (m + 1), (2 ^ (2 * j) - 1))
  have hodd := oddDoubleFactorial_mul_interval (k + 1) (m + 1)
    (Nat.succ_le_succ hk)
  have heven := evenMersenneProduct_mul_interval k m hk
  have hden :
      (oddDoubleFactorial (k + 1) * evenMersenneProduct k) * tail =
        oddDoubleFactorial (m + 1) * evenMersenneProduct m := by
    dsimp [tail]
    calc
      oddDoubleFactorial (k + 1) * evenMersenneProduct k *
            (oddFactorProduct (k + 1) (m + 1) *
              ∏ j ∈ Ico (k + 1) (m + 1), (2 ^ (2 * j) - 1)) =
          (oddDoubleFactorial (k + 1) * oddFactorProduct (k + 1) (m + 1)) *
            (evenMersenneProduct k *
              ∏ j ∈ Ico (k + 1) (m + 1), (2 ^ (2 * j) - 1)) := by
                ring
      _ = oddDoubleFactorial (m + 1) * evenMersenneProduct m := by
        rw [hodd, heven]
  have hdenNe :
      ((oddDoubleFactorial (k + 1) * evenMersenneProduct k : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      ((odd_oddDoubleFactorial (k + 1)).mul
        (odd_evenMersenneProduct k)).pos
  rw [moment_eq_momentNumerator_div]
  have hdenRat := congrArg (fun z : ℕ => (z : ℚ)) hden
  push_cast at hdenRat
  dsimp [commonMomentNumerator, tail]
  push_cast
  rw [← hdenRat]
  dsimp [tail]
  push_cast
  have hdenNe' :
      (oddDoubleFactorial (k + 1) : ℚ) * evenMersenneProduct k ≠ 0 := by
    simpa only [Nat.cast_mul] using hdenNe
  have hoddNe : (oddDoubleFactorial (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (odd_oddDoubleFactorial (k + 1)).pos
  have hevenNe : (evenMersenneProduct k : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (odd_evenMersenneProduct k).pos
  field_simp [hdenNe', hoddNe, hevenNe]

private def scaledDyadicInteger (n b : ℕ) : ℤ :=
  ∑ h : Fin b, thueMorseSign h.val *
    ∑ k : Fin (n / 2 + 1),
      (Nat.choose n (2 * k.val) : ℤ) *
        (2 * (b : ℤ) - 2 * (h.val : ℤ) - 1) ^ (n - 2 * k.val) *
        commonMomentNumerator (n / 2) k.val

private lemma fabiusDyadic_mul_denominatorBound_eq_int (n b : ℕ) :
    fabiusDyadic n b * (denominatorBound n : ℚ) =
      (scaledDyadicInteger n b : ℚ) := by
  unfold fabiusDyadic
  let C : ℕ := oddDoubleFactorial (n / 2 + 1) *
    evenMersenneProduct (n / 2)
  let S : ℚ := ∑ h : Fin b, (thueMorseSign h.val : ℚ) *
    ∑ k : Fin (n / 2 + 1),
      (Nat.choose n (2 * k.val) : ℚ) *
        ((2 : ℚ) * b - 2 * h.val - 1) ^ (n - 2 * k.val) * moment k.val
  have hboundCast : (denominatorBound n : ℚ) =
      (n.factorial : ℚ) * (2 : ℚ) ^ (n + 1).choose 2 * (C : ℚ) := by
    dsimp [denominatorBound, C]
    push_cast
    ring
  rw [hboundCast]
  change ((2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial * S) *
      ((n.factorial : ℚ) * (2 : ℚ) ^ (n + 1).choose 2 * C) = _
  have hnfac : (n.factorial : ℚ) ≠ 0 := by positivity
  have hpow : (2 : ℚ) ^ Nat.choose (n + 1) 2 ≠ 0 := by positivity
  have hcancel :
      (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) *
          (2 : ℚ) ^ Nat.choose (n + 1) 2 = 1 := by
    rw [zpow_neg, zpow_natCast]
    exact inv_mul_cancel₀ hpow
  have hscaled : S * (C : ℚ) = (scaledDyadicInteger n b : ℚ) := by
    dsimp [S, scaledDyadicInteger]
    rw [Finset.sum_mul]
    push_cast
    apply Finset.sum_congr rfl
    intro h hh
    rw [mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLe : k.val ≤ n / 2 := by omega
    rw [← moment_mul_common_denominator (n / 2) k.val hkLe]
    dsimp [C]
    push_cast
    ring
  rw [← hscaled]
  field_simp [hnfac]
  linear_combination S * (C : ℚ) * hcancel

/-- Scaling a closed-form dyadic value by the bound always gives an integer. -/
theorem fabiusDyadic_mul_denominatorBound_isInteger (n b : ℕ) :
    ∃ z : ℤ,
      fabiusDyadic n b * (denominatorBound n : ℚ) = (z : ℚ) :=
  ⟨scaledDyadicInteger n b,
    fabiusDyadic_mul_denominatorBound_eq_int n b⟩

/-- Taking the absolute value turns the integer scaling into a natural one. -/
theorem abs_fabiusDyadic_mul_denominatorBound_isNatural (n b : ℕ) :
    IsNatural (|fabiusDyadic n b| * denominatorBound n) := by
  let z := scaledDyadicInteger n b
  refine ⟨z.natAbs, ?_⟩
  have hboundNonneg : (0 : ℚ) ≤ denominatorBound n := by positivity
  calc
    |fabiusDyadic n b| * (denominatorBound n : ℚ) =
        |fabiusDyadic n b * denominatorBound n| := by
          rw [abs_mul, abs_of_nonneg hboundNonneg]
    _ = |(z : ℚ)| := by
      rw [fabiusDyadic_mul_denominatorBound_eq_int]
    _ = (z.natAbs : ℕ) := by
      norm_cast
      simp

/-- Every exact Rvachev value becomes natural after multiplication by the
bound from Theorem 13.  Outside the support the value is zero. -/
theorem rvachevDyadic_mul_denominatorBound_isNatural_all (n : ℕ) (a : ℤ) :
    IsNatural (rvachevDyadic n a * denominatorBound n) := by
  by_cases ha : a.natAbs ≤ 2 ^ n
  · rw [rvachevDyadic, if_pos ha]
    exact abs_fabiusDyadic_mul_denominatorBound_isNatural n
      (2 ^ n - a.natAbs)
  · rw [rvachevDyadic, if_neg ha, zero_mul]
    exact ⟨0, by norm_num⟩

/-- The supported-input form of
`rvachevDyadic_mul_denominatorBound_isNatural_all`, retained for compatibility
with the hypotheses in Theorem 13. -/
theorem rvachevDyadic_mul_denominatorBound_isNatural (n : ℕ) (a : ℤ)
    (ha : a.natAbs ≤ 2 ^ n) :
    IsNatural (rvachevDyadic n a * denominatorBound n) :=
  have _ := ha
  rvachevDyadic_mul_denominatorBound_isNatural_all n a

/-- The explicit common-denominator bound is strictly positive. -/
theorem denominatorBound_pos (n : ℕ) : 0 < denominatorBound n := by
  unfold denominatorBound
  exact Nat.mul_pos
    (Nat.mul_pos
      (Nat.mul_pos (Nat.factorial_pos n) (pow_pos (by omega) _))
      (oddDoubleFactorial_pos _))
    (evenMersenneProduct_pos _)

/-- Each closed-form dyadic Fabius value has reduced denominator dividing the
level's common denominator bound. -/
theorem fabiusDyadic_den_dvd_denominatorBound (n b : ℕ) :
    (fabiusDyadic n b).den ∣ denominatorBound n :=
  rat_den_dvd_of_mul_nat_eq_int
    (fabiusDyadic_mul_denominatorBound_eq_int n b)

/-- Each exact Rvachev value has reduced denominator dividing the level's
common denominator bound, including the values outside its support. -/
theorem rvachevDyadic_den_dvd_denominatorBound (n : ℕ) (a : ℤ) :
    (rvachevDyadic n a).den ∣ denominatorBound n := by
  obtain ⟨m, hm⟩ := rvachevDyadic_mul_denominatorBound_isNatural_all n a
  apply rat_den_dvd_of_mul_nat_eq_int (z := (m : ℤ))
  simpa using hm

/-- The LCM of all reduced denominators on the odd dyadic grid divides the
common denominator from Theorem 13. -/
theorem dyadicDenominator_dvd_denominatorBound (n : ℕ) :
    dyadicDenominator n ∣ denominatorBound n := by
  unfold dyadicDenominator
  apply Finset.lcm_dvd
  intro a _ha
  exact rvachevDyadic_den_dvd_denominatorBound n (a : ℤ)

end Fabius
