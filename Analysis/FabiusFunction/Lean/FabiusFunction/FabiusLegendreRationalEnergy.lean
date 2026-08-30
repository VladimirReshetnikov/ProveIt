import FabiusFunction.FabiusLegendreEnergy
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Rational Legendre energy of Rvachev's function

The even Fourier--Legendre coefficients of Rvachev's `up` function are real
integrals, but their finite dyadic formula shows that they are rational.  This
module records the rational objects themselves and connects them to the
analytic coefficients:

* `canonicalRvachevLegendreCoefficientRat` is the exact rational coefficient;
* its cast to `ℝ` is `rvachevLegendreCoefficient fabius`;
* `fabiusSquareEnergyTermRat` and `fabiusSquareEnergyPartialSumRat` package the
  rational terms and finite partial sums of the Legendre energy series;
* the casted rational terms have the same `HasSum` and `tsum` as the analytic
  coefficient energies.

Thus every finite approximation to the square energy `A₂` supplied by the
Legendre series is canonically rational, while its limit remains the real
integral `fabiusSquareEnergy fabius`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset
open Filter

namespace Fabius

/-- The exact rational value of the `n`-th even Rvachev--Legendre
coefficient.  This is the finite dyadic formula with each analytic Fabius
value replaced by its canonical rational evaluator. -/
def canonicalRvachevLegendreCoefficientRat (n : ℕ) : ℚ :=
  (4 : ℚ)⁻¹ ^ n * ((4 * n + 1 : ℕ) : ℚ) *
    ∑ k ∈ range (n + 1),
      (-1 : ℚ) ^ (n + k) *
        ((2 * n).choose (n + k) : ℚ) *
        ((2 * n + 2 * k).choose (2 * n) : ℚ) *
        (Nat.factorial (2 * k) : ℚ) *
        2 ^ (2 * k + 1).choose 2 *
        fabiusAtInverseTwoPow (2 * k + 1)

/-- Casting the canonical rational coefficient to `ℝ` recovers the analytic
Fourier--Legendre coefficient of Rvachev's `up` function. -/
theorem canonicalRvachevLegendreCoefficientRat_cast (n : ℕ) :
    (canonicalRvachevLegendreCoefficientRat n : ℝ) =
      rvachevLegendreCoefficient fabius n := by
  rw [canonical_rvachevLegendreCoefficient_eq_fabius_sum]
  unfold canonicalRvachevLegendreCoefficientRat
  push_cast
  apply congrArg₂ (· * ·) rfl
  apply Finset.sum_congr rfl
  intro k _hk
  rw [fabiusAtInverseTwoPow_cast fabius fabius_spec]

/-- The zeroth canonical rational Legendre coefficient is `1 / 2`. -/
@[simp] theorem canonicalRvachevLegendreCoefficientRat_zero :
    canonicalRvachevLegendreCoefficientRat 0 = 1 / 2 := by
  apply Rat.cast_injective (α := ℝ)
  rw [canonicalRvachevLegendreCoefficientRat_cast]
  rw [canonical_rvachevLegendreCoefficient_eq_fabius_sum 0]
  norm_num [fabius_half fabius fabius_spec]

/-- The `n`-th rational summand in the Legendre series for the Fabius square
energy `A₂`. -/
def fabiusSquareEnergyTermRat (n : ℕ) : ℚ :=
  canonicalRvachevLegendreCoefficientRat n ^ 2 /
    ((4 * n + 1 : ℕ) : ℚ)

/-- The rational energy term casts to the corresponding real Legendre
coefficient energy. -/
theorem fabiusSquareEnergyTermRat_cast (n : ℕ) :
    (fabiusSquareEnergyTermRat n : ℝ) =
      (rvachevLegendreCoefficient fabius n) ^ 2 /
        (((4 * n + 1 : ℕ) : ℝ)) := by
  simp only [fabiusSquareEnergyTermRat]
  push_cast
  rw [canonicalRvachevLegendreCoefficientRat_cast]

/-- Every exact rational Legendre-energy summand is nonnegative. -/
theorem fabiusSquareEnergyTermRat_nonneg (n : ℕ) :
    0 ≤ fabiusSquareEnergyTermRat n := by
  unfold fabiusSquareEnergyTermRat
  positivity

/-- The zeroth rational Legendre-energy summand is `1 / 4`. -/
@[simp] theorem fabiusSquareEnergyTermRat_zero :
    fabiusSquareEnergyTermRat 0 = 1 / 4 := by
  rw [fabiusSquareEnergyTermRat,
    canonicalRvachevLegendreCoefficientRat_zero]
  norm_num

/-- The `N`-th finite partial sum of the Legendre series for `A₂`, retained
as an exact rational number. -/
def fabiusSquareEnergyPartialSumRat (N : ℕ) : ℚ :=
  ∑ n ∈ range (N + 1), fabiusSquareEnergyTermRat n

/-- Every finite Legendre approximation to `A₂` is the real cast of the
canonical rational partial sum. -/
theorem fabiusSquareEnergyPartialSumRat_cast (N : ℕ) :
    (fabiusSquareEnergyPartialSumRat N : ℝ) =
      ∑ n ∈ range (N + 1),
        (rvachevLegendreCoefficient fabius n) ^ 2 /
          (((4 * n + 1 : ℕ) : ℝ)) := by
  rw [fabiusSquareEnergyPartialSumRat]
  push_cast
  apply Finset.sum_congr rfl
  intro n _hn
  simpa only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using
    fabiusSquareEnergyTermRat_cast n

/-- The exact rational partial sums increase monotonically with the cutoff. -/
theorem monotone_fabiusSquareEnergyPartialSumRat :
    Monotone fabiusSquareEnergyPartialSumRat := by
  apply monotone_nat_of_le_succ
  intro N
  change (∑ n ∈ range (N + 1), fabiusSquareEnergyTermRat n) ≤
    ∑ n ∈ range ((N + 1) + 1), fabiusSquareEnergyTermRat n
  nth_rewrite 2 [Finset.sum_range_succ]
  have hnonneg : 0 ≤ fabiusSquareEnergyTermRat (N + 1) :=
    fabiusSquareEnergyTermRat_nonneg (N + 1)
  have hadd := add_le_add_left hnonneg
    (∑ n ∈ range (N + 1), fabiusSquareEnergyTermRat n)
  simpa only [zero_add, add_zero, add_comm] using hadd

/-- Every canonical rational Legendre-energy partial sum is strictly
positive. -/
theorem fabiusSquareEnergyPartialSumRat_pos (N : ℕ) :
    0 < fabiusSquareEnergyPartialSumRat N := by
  have hle :
      fabiusSquareEnergyTermRat 0 ≤ fabiusSquareEnergyPartialSumRat N := by
    rw [fabiusSquareEnergyPartialSumRat]
    exact Finset.single_le_sum
      (fun n _hn => fabiusSquareEnergyTermRat_nonneg n) (by simp)
  rw [fabiusSquareEnergyTermRat_zero] at hle
  exact lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1 / 4) hle

/-- The zeroth rational Legendre-energy partial sum is `1 / 4`. -/
@[simp] theorem fabiusSquareEnergyPartialSumRat_zero :
    fabiusSquareEnergyPartialSumRat 0 = 1 / 4 := by
  native_decide

/-- The first rational Legendre-energy partial sum is `7 / 18`. -/
theorem fabiusSquareEnergyPartialSumRat_one :
    fabiusSquareEnergyPartialSumRat 1 = 7 / 18 := by
  native_decide

/-- The second rational Legendre-energy partial sum is `3271 / 8100`. -/
theorem fabiusSquareEnergyPartialSumRat_two :
    fabiusSquareEnergyPartialSumRat 2 = 3271 / 8100 := by
  native_decide

/-- The third rational Legendre-energy partial sum is
`3246043 / 8037225`. -/
theorem fabiusSquareEnergyPartialSumRat_three :
    fabiusSquareEnergyPartialSumRat 3 = 3246043 / 8037225 := by
  native_decide

/-- The real casts of the exact rational energy terms sum to the square
energy `A₂`. -/
theorem hasSum_fabiusSquareEnergy_ratCast :
    HasSum (fun n : ℕ => (fabiusSquareEnergyTermRat n : ℝ))
      (fabiusSquareEnergy fabius) := by
  simpa only [fabiusSquareEnergyTermRat_cast] using
    hasSum_fabiusSquareEnergy_legendre fabius fabius_spec

/-- `tsum` form of the rational-term Legendre series for `A₂`. -/
theorem fabiusSquareEnergy_eq_tsum_ratCast :
    fabiusSquareEnergy fabius =
      ∑' n : ℕ, (fabiusSquareEnergyTermRat n : ℝ) :=
  hasSum_fabiusSquareEnergy_ratCast.tsum_eq.symm

/-- The real casts of the canonical rational partial sums converge to the
Fabius square energy. -/
theorem tendsto_fabiusSquareEnergyPartialSumRat_cast :
    Tendsto (fun N : ℕ => (fabiusSquareEnergyPartialSumRat N : ℝ)) atTop
      (nhds (fabiusSquareEnergy fabius)) := by
  have h := hasSum_fabiusSquareEnergy_ratCast.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)
  convert h using 1
  funext N
  simp only [Function.comp_apply, fabiusSquareEnergyPartialSumRat]
  push_cast
  rfl

end Fabius
