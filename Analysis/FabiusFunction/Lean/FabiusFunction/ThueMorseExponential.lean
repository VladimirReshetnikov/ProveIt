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

/-! ## Removing the explicit powers of `X` -/

/-- The rational formal series `(exp X - 1) / X`. -/
noncomputable def rationalExpm1DivSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => 1 / ((n + 1).factorial : ℚ)

@[simp] theorem coeff_rationalExpm1DivSeries (n : ℕ) :
    PowerSeries.coeff n rationalExpm1DivSeries =
      1 / ((n + 1).factorial : ℚ) := by
  simp [rationalExpm1DivSeries]

/-- Denominator-cleared characterization of `(exp X - 1) / X`. -/
theorem X_mul_rationalExpm1DivSeries :
    (PowerSeries.X : PowerSeries ℚ) * rationalExpm1DivSeries =
      PowerSeries.exp ℚ - 1 := by
  ext (_ | n)
  · simp
  · simp [rationalExpm1DivSeries, PowerSeries.coeff_exp]

/-- Each factor `1 - exp (-a X)` has one explicit factor `a X`. -/
theorem one_sub_rescale_neg_exp_eq (a : ℚ) :
    1 - PowerSeries.rescale (-a) (PowerSeries.exp ℚ) =
      PowerSeries.C a * PowerSeries.X *
        PowerSeries.rescale (-a) rationalExpm1DivSeries := by
  have h := congrArg (PowerSeries.rescale (-a))
    X_mul_rationalExpm1DivSeries
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at h
  calc
    1 - PowerSeries.rescale (-a) (PowerSeries.exp ℚ) =
        -(PowerSeries.rescale (-a) (PowerSeries.exp ℚ) - 1) := by ring
    _ = -(PowerSeries.C (-a) * PowerSeries.X *
          PowerSeries.rescale (-a) rationalExpm1DivSeries) := by rw [h]
    _ = _ := by simp

/-- Extract all `X`-powers and dyadic scalar factors from the finite product. -/
theorem prod_one_sub_rescale_neg_exp_eq (k : ℕ) :
    (∏ j ∈ Finset.range k,
        (1 - PowerSeries.rescale (-(2 : ℚ) ^ j) (PowerSeries.exp ℚ))) =
      PowerSeries.C ((2 : ℚ) ^ k.choose 2) * PowerSeries.X ^ k *
        ∏ j ∈ Finset.range k,
          PowerSeries.rescale (-(2 : ℚ) ^ j) rationalExpm1DivSeries := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hchoose : (k + 1).choose 2 = k.choose 2 + k := by
        rw [show k + 1 = Nat.succ k by omega, Nat.choose_succ_succ]
        simp [Nat.choose_one_right, add_comm]
      rw [Finset.prod_range_succ, ih,
        one_sub_rescale_neg_exp_eq, hchoose, pow_add, pow_succ]
      rw [Finset.prod_range_succ]
      simp only [map_mul]
      ring

/-- Normalized factorization of the shifted inner-sum series.  The scalar
`(-1)^k 2^(k choose 2)` is the precise normalization left after cancelling
the forced factor `X^k`. -/
theorem thueMorseShiftedPowerSeries_eq_expm1_product (k : ℕ) :
    thueMorseShiftedPowerSeries k =
      PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
        (PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) *
          ∏ j ∈ Finset.range k,
            PowerSeries.rescale (-(2 : ℚ) ^ j) rationalExpm1DivSeries) := by
  apply PowerSeries.X_pow_mul_cancel (k := k)
  rw [X_pow_mul_thueMorseShiftedPowerSeries,
    thueMorseCenteredPowerSeries_eq_product,
    prod_one_sub_rescale_neg_exp_eq]
  rw [Algebra.smul_def]
  change PowerSeries.C ((-1 : ℚ) ^ k) * _ = _
  rw [map_mul]
  ring

/-- Iterating `A(2X) = ((exp X - 1) / X) A(X)` along the negative dyadic
orbit absorbs the finite product occurring above. -/
theorem prod_rescale_neg_expm1_mul_rescale_neg_one
    (A : PowerSeries ℚ)
    (hA : PowerSeries.rescale 2 A = rationalExpm1DivSeries * A)
    (k : ℕ) :
    (∏ j ∈ Finset.range k,
        PowerSeries.rescale (-(2 : ℚ) ^ j) rationalExpm1DivSeries) *
        PowerSeries.rescale (-1 : ℚ) A =
      PowerSeries.rescale (-(2 : ℚ) ^ k) A := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ]
      calc
        ((∏ j ∈ Finset.range k,
              PowerSeries.rescale (-(2 : ℚ) ^ j) rationalExpm1DivSeries) *
            PowerSeries.rescale (-(2 : ℚ) ^ k) rationalExpm1DivSeries) *
              PowerSeries.rescale (-1 : ℚ) A =
            ((∏ j ∈ Finset.range k,
                PowerSeries.rescale (-(2 : ℚ) ^ j) rationalExpm1DivSeries) *
              PowerSeries.rescale (-1 : ℚ) A) *
                PowerSeries.rescale (-(2 : ℚ) ^ k)
                  rationalExpm1DivSeries := by ring
        _ = PowerSeries.rescale (-(2 : ℚ) ^ k) A *
              PowerSeries.rescale (-(2 : ℚ) ^ k)
                rationalExpm1DivSeries := by rw [ih]
        _ = PowerSeries.rescale (-(2 : ℚ) ^ k)
              (A * rationalExpm1DivSeries) := by rw [map_mul]
        _ = PowerSeries.rescale (-(2 : ℚ) ^ k)
              (PowerSeries.rescale 2 A) := by rw [hA]; congr 1; ring
        _ = PowerSeries.rescale (-(2 : ℚ) ^ (k + 1)) A := by
          rw [PowerSeries.rescale_rescale]
          congr 1
          rw [pow_succ]
          ring

/-- Refinement-ready form of the inner-sum identity.  Any formal series
satisfying the Fabius moment functional equation absorbs the entire finite
product into one negative dyadic rescaling. -/
theorem thueMorseShiftedPowerSeries_mul_of_rescale_two
    (A : PowerSeries ℚ)
    (hA : PowerSeries.rescale 2 A = rationalExpm1DivSeries * A)
    (k : ℕ) :
    thueMorseShiftedPowerSeries k * PowerSeries.rescale (-1 : ℚ) A =
      PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
        (PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) *
          PowerSeries.rescale (-(2 : ℚ) ^ k) A) := by
  rw [thueMorseShiftedPowerSeries_eq_expm1_product]
  calc
    (PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
          (PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) *
            ∏ j ∈ Finset.range k,
              PowerSeries.rescale (-(2 : ℚ) ^ j) rationalExpm1DivSeries)) *
        PowerSeries.rescale (-1 : ℚ) A =
      PowerSeries.C (((-1 : ℚ) ^ k) * (2 : ℚ) ^ k.choose 2) *
        (PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ) *
          ((∏ j ∈ Finset.range k,
              PowerSeries.rescale (-(2 : ℚ) ^ j) rationalExpm1DivSeries) *
            PowerSeries.rescale (-1 : ℚ) A)) := by ring
    _ = _ := by rw [prod_rescale_neg_expm1_mul_rescale_neg_one A hA k]

end Fabius
