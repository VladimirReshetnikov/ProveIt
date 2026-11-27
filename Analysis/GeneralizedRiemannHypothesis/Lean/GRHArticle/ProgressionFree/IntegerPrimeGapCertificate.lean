import GRHArticle.ProgressionFree.IntegerDyadicArithmetic
import GRHArticle.ProgressionFree.IntegerWheelTail
import GRHArticle.ProgressionFree.IntegerPrefixEightyExact
import GRHArticle.ProgressionFree.IntegerPrefixTransfer
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Prime-product and prime-square certificates for McNew's density gaps

Bound the prime-square sum above 83 or 293 through 16383 with
upward-rounded integer weights. Every prime exceeding 128 is coprime to
128!, so discarding multiples of its factors is sound without a primality
test on each large candidate. The infinite remainder is bounded analytically.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private def scale : ℕ := 10^14

private def sieveCandidate (p : ℕ) : Bool :=
  if p ≤ 128 then decide p.Prime else decide (p.Coprime (Nat.factorial 128))

private theorem sieveCandidate_prime {p : ℕ} (hp : p.Prime) : sieveCandidate p = true := by
  dsimp [sieveCandidate]
  split <;> rename_i h
  · exact decide_eq_true hp
  · exact decide_eq_true (hp.coprime_factorial_of_lt (by omega))

private def upperWeight (Y p : ℕ) : ℕ :=
  if Y < p && sieveCandidate p then scale / p^2 + 1 else 0

private theorem integerPrimeSquareTerm_le_upperWeight (Y p : ℕ) :
    integerPrimeSquareTerm Y p ≤ (upperWeight Y p : ℝ) / scale := by
  have hs : 0 < (scale : ℝ) := by norm_num [scale]
  by_cases h : Y < p ∧ p.Prime
  · have hp : 0 < (p : ℝ)^2 := pow_pos (Nat.cast_pos.mpr h.2.pos) _
    simp only [integerPrimeSquareTerm, if_pos h, upperWeight, decide_eq_true h.1,
      sieveCandidate_prime h.2, Bool.and_self, ↓reduceIte]
    apply (div_le_div_iff₀ hp hs).mpr
    rw [one_mul, mul_comm]
    exact_mod_cast (Nat.lt_mul_div_succ scale (pow_pos h.2.pos 2)).le
  · rw [integerPrimeSquareTerm, if_neg h]
    positivity

theorem integerDyadicSum_eq (f : ℕ → ℕ) (h a : ℕ) :
    integerDyadicSum f h a = ∑ i ∈ range (2^h), f (a+i) := by
  induction h generalizing a with
  | zero => simp [integerDyadicSum]
  | succ h ih =>
    rw [integerDyadicSum, ih, ih, pow_succ, Nat.mul_two, sum_range_add]
    simp only [Nat.add_assoc]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem finite_prime_square_bounds :
    integerDyadicSum (upperWeight 293) 14 0 ≤ 48517433775 ∧
      integerDyadicSum (upperWeight 83) 14 0 ≤ 204544244887 := by decide +kernel

private theorem tail_le_certified {Y B : ℕ} (hY : Y ≤ 16383)
    (h : integerDyadicSum (upperWeight Y) 14 0 ≤ B) :
    integerPrimeSquareTail Y ≤ (B : ℝ)/scale + (48:ℝ)/210^2/77 := by
  rw [integerPrimeSquareTail_split hY]
  apply add_le_add _ integerPrimeSquareTail_wheel_bound
  calc
    _ ≤ ∑ p ∈ range (16383+1), (upperWeight Y p : ℝ)/scale :=
      sum_le_sum (fun p _ ↦ integerPrimeSquareTerm_le_upperWeight Y p)
    _ = (integerDyadicSum (upperWeight Y) 14 0 : ℝ) / scale := by
      rw [integerDyadicSum_eq, Nat.cast_sum, sum_div]
      simp only [Nat.zero_add]
      rfl
    _ ≤ _ := div_le_div_of_nonneg_right (Nat.cast_le.mpr h) (Nat.cast_nonneg _)

private def roughProduct (Y : ℕ) : ℚ := ∏ p ∈ Nat.primesLE Y, (1-(p:ℚ)⁻¹)

private theorem roughProduct_cast (Y : ℕ) : (roughProduct Y : ℝ) = integerSmoothDensityFactor Y := by
  simp only [roughProduct, integerSmoothDensityFactor, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
    Rat.cast_inv, Rat.cast_natCast]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finite_rough_products :
    (974585493:ℚ)/10^10 ≤ roughProduct 293 ∧ (1229520796:ℚ)/10^10 ≤ roughProduct 83 := by
  decide +kernel

/-- Numerical margin for rational ratios at `N=80` and `Y=293`, with the
entire prime-square tail included. -/
theorem rationalPrimePrefix_margin :
    (2836:ℝ)/1000000 < integerSmoothDensityFactor 293 * (integerPrefixLoss false 80 : ℝ) -
      integerPrimeSquareTail 293 := by
  have ht := tail_le_certified (Y := 293) (by decide) finite_prime_square_bounds.1
  have hc := (Rat.cast_le (K := ℝ)).mpr finite_rough_products.1
  rw [roughProduct_cast] at hc
  rw [integerPrefixLoss_eighty]
  norm_num [scale, Rat.cast_div] at hc ht ⊢
  linarith

/-- Numerical margin for integral ratios obtained from the same prefix with
`Y=83`. -/
theorem integralPrimePrefix_margin :
    (13336:ℝ)/1000000 < integerSmoothDensityFactor 83 * (integerPrefixLoss true 80 : ℝ) -
      integerPrimeSquareTail 83 := by
  have ht := tail_le_certified (Y := 83) (by decide) finite_prime_square_bounds.2
  have hc := (Rat.cast_le (K := ℝ)).mpr finite_rough_products.2
  rw [roughProduct_cast] at hc
  rw [integerPrefixLoss_eighty]
  norm_num [scale, Rat.cast_div] at hc ht ⊢
  linarith

end GRHArticle.ProgressionFree
