import FabiusFunction.ThueMorseGenerating
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Exponential series for centered Thue--Morse power sums

This module isolates the inner finite sum in the explicit inverse-power
formula for the Fabius function.  The Wolfram Language expression

`Sum[(-1)^ThueMorse[r] (r - 2^k)^m, {r, 0, 2^k - 1}]`

is represented by `thueMorseCenteredPowerSum k m`.  Its subtraction takes
place in `ℚ`, not in `ℕ`; `thueMorseCenteredPowerSum_eq_intCast` verifies
that this is exactly the cast of the corresponding integer sum.

The main algebraic result packages the normalized sums into a formal power
series.  The first `k` coefficients vanish by Prouhet cancellation, so the
exponential generating series is divisible by `X^k`.  After removing this
forced zero, its coefficient of degree `n` is precisely

`thueMorseCenteredPowerSum k (n + k) / (n + k)!`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- The integer-valued centered signed power sum underlying the Wolfram
Language expression. -/
def thueMorseCenteredPowerSumInt (k m : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (2 ^ k),
    thueMorseSign r * ((r : ℤ) - (2 ^ k : ℕ)) ^ m

/-- The centered signed power sum in rational arithmetic.  Rational
arithmetic is the convenient form for the outer inverse-power formula. -/
def thueMorseCenteredPowerSum (k m : ℕ) : ℚ :=
  ∑ r : Fin (2 ^ k),
    (thueMorseSign r.val : ℚ) *
      ((r.val : ℚ) - (2 : ℚ) ^ k) ^ m

/-- The rational inner sum is exactly the cast of its integer interpretation. -/
theorem thueMorseCenteredPowerSum_eq_intCast (k m : ℕ) :
    thueMorseCenteredPowerSum k m =
      (thueMorseCenteredPowerSumInt k m : ℚ) := by
  rw [thueMorseCenteredPowerSum, thueMorseCenteredPowerSumInt,
    Fin.sum_univ_eq_sum_range
      (fun r : ℕ =>
        (thueMorseSign r : ℚ) *
          ((r : ℚ) - (2 : ℚ) ^ k) ^ m)
      (2 ^ k)]
  push_cast
  norm_num

/-- Range-indexed form, matching the bounds printed by Wolfram Language. -/
theorem thueMorseCenteredPowerSum_eq_sum_range (k m : ℕ) :
    thueMorseCenteredPowerSum k m =
      ∑ r ∈ Finset.range (2 ^ k),
        (thueMorseSign r : ℚ) *
          ((r : ℚ) - (2 : ℚ) ^ k) ^ m := by
  rw [thueMorseCenteredPowerSum,
    Fin.sum_univ_eq_sum_range
      (fun r : ℕ =>
        (thueMorseSign r : ℚ) *
          ((r : ℚ) - (2 : ℚ) ^ k) ^ m)
      (2 ^ k)]

/-- At `k = 0`, the inner block consists only of `r = 0`. -/
@[simp] theorem thueMorseCenteredPowerSum_zero (m : ℕ) :
    thueMorseCenteredPowerSum 0 m = (-1 : ℚ) ^ m := by
  simp [thueMorseCenteredPowerSum, thueMorseSign, binaryWeight]

/-- Prouhet cancellation: a dyadic block of exponent `k` annihilates every
polynomial of degree strictly below `k`. -/
theorem thueMorseCenteredPowerSum_eq_zero_of_lt
    (k m : ℕ) (hm : m < k) :
    thueMorseCenteredPowerSum k m = 0 := by
  have hzero := thueMorse_affine_power_sum_eq_zero k m hm
    (-(2 : ℚ) ^ k) 1
  rw [thueMorseCenteredPowerSum]
  convert hzero using 1
  ring_nf

/-- The finite exponential generating series before removing its forced
zero of order `k`. -/
noncomputable def thueMorseCenteredPowerSeries (k : ℕ) : PowerSeries ℚ :=
  ∑ r : Fin (2 ^ k), (thueMorseSign r.val : ℚ) •
    PowerSeries.rescale ((r.val : ℚ) - (2 : ℚ) ^ k)
      (PowerSeries.exp ℚ)

/-- Coefficients of the finite exponential series recover the centered
power sums divided by factorials. -/
@[simp] theorem coeff_thueMorseCenteredPowerSeries (k m : ℕ) :
    PowerSeries.coeff m (thueMorseCenteredPowerSeries k) =
      thueMorseCenteredPowerSum k m / m.factorial := by
  rw [thueMorseCenteredPowerSum]
  simp only [thueMorseCenteredPowerSeries, map_sum,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp, map_smul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _hr
  simp only [smul_eq_mul]
  norm_num
  ring

/-- The centered exponential series at the empty binary scale. -/
@[simp] theorem thueMorseCenteredPowerSeries_zero :
    thueMorseCenteredPowerSeries 0 =
      PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) := by
  ext m
  simp [thueMorseCenteredPowerSeries, thueMorseSign, binaryWeight]

private noncomputable abbrev ratExpSeries (a : ℚ) : PowerSeries ℚ :=
  PowerSeries.rescale a (PowerSeries.exp ℚ)

private theorem centered_exp_first (k : ℕ) (r : Fin (2 ^ k)) :
    (thueMorseSign r.val : ℚ) •
        ratExpSeries ((r.val : ℚ) - (2 : ℚ) ^ (k + 1)) =
      ((thueMorseSign r.val : ℚ) •
          ratExpSeries ((r.val : ℚ) - (2 : ℚ) ^ k)) *
        ratExpSeries (-(2 : ℚ) ^ k) := by
  rw [smul_mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]
  congr 2
  rw [pow_succ]
  ring

private theorem centered_exp_second (k : ℕ) (r : Fin (2 ^ k)) :
    (thueMorseSign (2 ^ k + r.val) : ℚ) •
        ratExpSeries
          (((2 ^ k + r.val : ℕ) : ℚ) - (2 : ℚ) ^ (k + 1)) =
      -((thueMorseSign r.val : ℚ) •
          ratExpSeries ((r.val : ℚ) - (2 : ℚ) ^ k)) := by
  rw [thueMorseSign_add_pow_two k r.val r.isLt]
  push_cast
  rw [neg_smul, pow_succ]
  congr 2
  ring

/-- Splitting a dyadic block into its two Thue--Morse halves gives the
one-step exponential-series recurrence. -/
theorem thueMorseCenteredPowerSeries_succ (k : ℕ) :
    thueMorseCenteredPowerSeries (k + 1) =
      thueMorseCenteredPowerSeries k *
        (PowerSeries.rescale (-(2 : ℚ) ^ k) (PowerSeries.exp ℚ) - 1) := by
  rw [thueMorseCenteredPowerSeries,
    show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by rw [pow_succ]; omega,
    Fin.sum_univ_add]
  rw [thueMorseCenteredPowerSeries, Finset.sum_mul]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  simp_rw [centered_exp_first, centered_exp_second]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg]
  simp_rw [mul_sub, mul_one]
  rw [← Finset.sum_sub_distrib]

/-- The coefficient series with the forced order-`k` zero removed.  Its
degree-`n` coefficient is exactly the normalized inner summand used in the
explicit inverse-power formula. -/
noncomputable def thueMorseShiftedPowerSeries (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    thueMorseCenteredPowerSum k (n + k) / (n + k).factorial

@[simp] theorem coeff_thueMorseShiftedPowerSeries (k n : ℕ) :
    PowerSeries.coeff n (thueMorseShiftedPowerSeries k) =
      thueMorseCenteredPowerSum k (n + k) / (n + k).factorial := by
  simp [thueMorseShiftedPowerSeries]

/-- Multiplying the shifted coefficient series by `X^k` recovers the full
finite exponential generating series. -/
theorem X_pow_mul_thueMorseShiftedPowerSeries (k : ℕ) :
    PowerSeries.X ^ k * thueMorseShiftedPowerSeries k =
      thueMorseCenteredPowerSeries k := by
  ext m
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hkm : k ≤ m
  · rw [if_pos hkm, coeff_thueMorseShiftedPowerSeries,
      coeff_thueMorseCenteredPowerSeries, Nat.sub_add_cancel hkm]
  · rw [if_neg hkm, coeff_thueMorseCenteredPowerSeries,
      thueMorseCenteredPowerSum_eq_zero_of_lt k m (Nat.lt_of_not_ge hkm)]
    norm_num

/-- Product factorization of the centered Thue--Morse exponential series. -/
theorem thueMorseCenteredPowerSeries_eq_product (k : ℕ) :
    thueMorseCenteredPowerSeries k =
      ((-1 : ℚ) ^ k) •
        (PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) *
          ∏ j ∈ Finset.range k,
            (1 - PowerSeries.rescale (-(2 : ℚ) ^ j)
              (PowerSeries.exp ℚ))) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [show k + 1 = k.succ by omega,
        thueMorseCenteredPowerSeries_succ, ih,
        Finset.prod_range_succ, pow_succ]
      rw [smul_mul_assoc, mul_smul, neg_one_smul]
      congr 1
      ring

/-- The exact shifted/product bridge used to replace every normalized inner
sum in the outer `q`-binomial expression. -/
theorem X_pow_mul_thueMorseShiftedPowerSeries_eq_product (k : ℕ) :
    PowerSeries.X ^ k * thueMorseShiftedPowerSeries k =
      ((-1 : ℚ) ^ k) •
        (PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) *
          ∏ j ∈ Finset.range k,
            (1 - PowerSeries.rescale (-(2 : ℚ) ^ j)
              (PowerSeries.exp ℚ))) := by
  rw [X_pow_mul_thueMorseShiftedPowerSeries,
    thueMorseCenteredPowerSeries_eq_product]

/-- The `k = 0` shifted series is simply `exp (-X)`. -/
@[simp] theorem thueMorseShiftedPowerSeries_zero :
    thueMorseShiftedPowerSeries 0 =
      PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) := by
  simpa using X_pow_mul_thueMorseShiftedPowerSeries 0

end Fabius
