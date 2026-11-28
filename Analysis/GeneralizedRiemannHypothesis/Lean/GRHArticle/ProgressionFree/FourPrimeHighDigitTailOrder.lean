import GRHArticle.ProgressionFree.FourPrimeHighDigitNumerics
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Positivity

/-!
# The high-digit bound decreases with the primes

All three explicit tail margins persist when a base prime increases.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The high-digit tail bound is antitone in the four base denominators. -/
theorem fourPrimeHighDigitTail_le_of_le {b q : Fin 4 → ℚ}
    (hb : ∀ i, 1 < b i) (hq : ∀ i, b i ≤ q i) :
    fourPrimeHighDigitTail q ≤ fourPrimeHighDigitTail b := by
  have hb₀ (i) : 0 < b i := zero_lt_one.trans (hb i)
  have hq₀ (i) : 0 < q i := (hb₀ i).trans_le (hq i)
  have hPow (i : Fin 4) (n : ℕ) : 1/q i^n ≤ 1/b i^n :=
    one_div_le_one_div_of_le (pow_pos (hb₀ i) _) (pow_le_pow_left₀ (hb₀ i).le (hq i) _)
  have hSub (i : Fin 4) {n : ℕ} (hn : n ≠ 0) : 0 < 1-1/b i^n :=
    sub_pos.mpr ((div_lt_one (pow_pos (hb₀ i) _)).mpr (one_lt_pow₀ (hb i) hn))
  have hLow₀ (a : Fin 4 → ℚ) (ha : ∀ i, 0 < a i) (e : Fin 2) :
      0 ≤ ∏ i : Fin 4, ∏ j ∈ range (fourPrimeLowDigitDepth i),
        (1 + 1 / a i ^ ((e.val+1)*3^j)) := by
    exact prod_nonneg fun i _ ↦ prod_nonneg fun j _ ↦
      add_nonneg zero_le_one (div_nonneg zero_le_one (pow_nonneg (ha i).le _))
  unfold fourPrimeHighDigitTail
  apply sum_le_sum
  intro e _
  let n (i : Fin 4) := (e.val+1)*3^(fourPrimeLowDigitDepth i)
  have hExp (i : Fin 4) : n i ≠ 0 := by dsimp [n]; positivity
  have hHigh (i : Fin 4) : (1-1/q i^n i)⁻¹ ≤ (1-1/b i^n i)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (hSub i (hExp i)) (sub_le_sub_left (hPow i (n i)) 1)
  have hHighPos (i : Fin 4) : 0 < 1-1/q i^n i :=
    (hSub i (hExp i)).trans_le (sub_le_sub_left (hPow i (n i)) 1)
  refine mul_le_mul ?_ ?_ ?_ (hLow₀ b hb₀ e)
  · apply prod_le_prod
    · intro i _
      exact prod_nonneg fun j _ ↦ add_nonneg zero_le_one (div_nonneg zero_le_one (pow_nonneg (hq₀ i).le _))
    · intro i _
      exact prod_le_prod
        (fun j _ ↦ add_nonneg zero_le_one (div_nonneg zero_le_one (pow_nonneg (hq₀ i).le _)))
        (fun j _ ↦ add_le_add_right (hPow i _) 1)
  · exact sub_le_sub_right (prod_le_prod (fun i _ ↦ (inv_pos.mpr (hHighPos i)).le) (fun i _ ↦ hHigh i)) 1
  · apply sub_nonneg.mpr
    apply one_le_prod
    intro i _
    have hqLow : 1-1/q i^n i ≤ 1 :=
      sub_le_self _ (div_nonneg zero_le_one (pow_nonneg (hq₀ i).le _))
    simpa only [one_div,inv_one] using one_div_le_one_div_of_le (hHighPos i) hqLow

end GRHArticle.ProgressionFree
