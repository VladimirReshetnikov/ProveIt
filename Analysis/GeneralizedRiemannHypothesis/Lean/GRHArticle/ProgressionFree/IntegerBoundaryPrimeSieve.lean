import GRHArticle.ProgressionFree.IntegerBoundarySieveData
import GRHArticle.ProgressionFree.IntegerPrimeGapCertificate

/-!
# Finite sieve for the inverse-square tail above 6619

Retain every integer coprime to the primes through 311. This overcounts
the primes above 6619. Round each surviving inverse-square contribution
upward on a fixed integer scale. Each of the 64 blocks of 8192 indices
can be checked independently.
-/

namespace GRHArticle.ProgressionFree

open Finset

open IntegerBoundarySieve

private theorem sieve_divides : 30030 ∣ Nat.factorial 311 ∧ sieveDivisor ∣ Nat.factorial 311 := by
  decide +kernel

private theorem primeTerm_le (p : ℕ) : integerPrimeSquareTerm 6619 p ≤ (weight p : ℝ)/scale := by
  by_cases h : 6619 < p ∧ p.Prime
  · have hc := h.2.coprime_factorial_of_lt (by omega : 311 < p)
    have h₁ := Nat.Coprime.of_dvd_right sieve_divides.1 hc
    have h₂ := Nat.Coprime.of_dvd_right sieve_divides.2 hc
    simp only [integerPrimeSquareTerm, if_pos h, weight, decide_eq_true h.1, show (p.gcd 30030 == 1) = true from beq_iff_eq.mpr h₁,
      show (p.gcd sieveDivisor == 1) = true from beq_iff_eq.mpr h₂, Bool.and_self, ↓reduceIte]
    apply (div_le_div_iff₀ (pow_pos (Nat.cast_pos.mpr h.2.pos) _) (by norm_num [scale])).mpr
    rw [one_mul,mul_comm]
    exact_mod_cast (Nat.lt_mul_div_succ scale (pow_pos h.2.pos 2)).le
  · rw [integerPrimeSquareTerm,if_neg h]
    positivity

private theorem blocks_sum (n : ℕ) :
    (∑ p ∈ range (8192*n), weight p) = ∑ i ∈ range n, block i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, sum_range_succ (f := block), ih,block,integerDyadicSum_eq]
    rfl

private theorem finite_bound : (∑ p ∈ range (524287+1), weight p) ≤ 15393623944 := by
  rw [show 524287+1 = 8192*64 by decide, blocks_sum]
  exact (sum_le_sum (fun i hi ↦ blocks_checked i (mem_range.mp hi))).trans_eq
    (by decide +kernel : (∑ i ∈ range 64, budget i) = 15393623944)

/-- The bound includes every prime above 6619, using the wheel estimate
beyond the finite sieve. -/
theorem integerPrimeSquareTail_6619_upper :
    integerPrimeSquareTail 6619 ≤ (15393623944:ℝ)/10^15 + (48:ℝ)/210^2/2495 := by
  rw [integerPrimeSquareTail_split (by decide : 6619 ≤ 524287)]
  apply add_le_add _ (integerPrimeSquareTail_le_wheel (by decide) (by decide))
  calc
    _ ≤ ∑ p ∈ range (524287+1), (weight p:ℝ)/scale := sum_le_sum (fun p _ ↦ primeTerm_le p)
    _ = ((∑ p ∈ range (524287+1), weight p : ℕ):ℝ)/scale := by rw [Nat.cast_sum, sum_div]
    _ ≤ (15393623944:ℕ)/ (scale:ℝ) := div_le_div_of_nonneg_right (Nat.cast_le.mpr finite_bound) (Nat.cast_nonneg _)
    _ = _ := by norm_num [scale]

end GRHArticle.ProgressionFree
