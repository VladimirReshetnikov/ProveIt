import GRHArticle.ProgressionFree.IntegerPrimeSquareTail
import Mathlib.Data.Nat.GCD.Basic

/-!
# Bounding the infinite prime tail by its 48 possible residues modulo 210

Starting at 16384, group the summands in blocks of 210. Within each block
only residues coprime to 210 can contribute. Telescoping the inverse-square
bounds on those blocks replaces a much longer finite sieve.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped BigOperators

private noncomputable def wheel (L j : ℕ) : ℝ := if L < j then (48/210^2) * (1/(j:ℝ)^2) else 0

private theorem wheel_block {K L : ℕ} (hL : 0 < L) (hK : 210*(L+1) ≤ K+1) (j : ℕ) :
    (∑ r ∈ range 210, integerPrimeSquareTerm K (210*j + r)) ≤ wheel L j := by
  let R := (range 210).filter (fun r ↦ r.Coprime 210)
  have hR : R.card = 48 := by decide
  by_cases hj : L < j
  · have hpos : 0 < (210:ℝ) * j := by
      exact mul_pos (by norm_num) (Nat.cast_pos.mpr (by omega))
    calc
      _ ≤ ∑ r ∈ range 210, if r.Coprime 210 then 1/((210:ℝ)*j)^2 else 0 := by
        refine sum_le_sum fun r _ ↦ ?_
        by_cases h : K < 210*j+r ∧ (210*j+r).Prime
        · have hc : (210*j+r).Coprime 210 := h.2.coprime_iff_not_dvd.mpr (by
            intro hd; have := Nat.le_of_dvd (by decide : 0 < 210) hd; omega)
          have hr : r.Coprime 210 := by simpa only [Nat.coprime_mul_left_add_left] using hc
          rw [integerPrimeSquareTerm, if_pos h, if_pos hr]
          apply one_div_le_one_div_of_le (sq_pos_of_pos hpos)
          push_cast
          exact pow_le_pow_left₀ hpos.le (le_add_of_nonneg_right (Nat.cast_nonneg r)) _
        · rw [integerPrimeSquareTerm, if_neg h]
          split <;> positivity
      _ = _ := by
        rw [← sum_filter]
        change (∑ _r ∈ R, (1:ℝ)/((210:ℝ)*j)^2) = _
        rw [sum_const, hR, nsmul_eq_mul, wheel, if_pos hj]
        push_cast
        ring
  · rw [wheel, if_neg hj]
    apply le_of_eq
    exact sum_eq_zero fun r hr ↦ if_neg (fun h ↦ by have := mem_range.mp hr; omega)

/-- Above a complete block boundary, only 48 of every 210 residues can
contribute to the inverse-square tail. -/
theorem integerPrimeSquareTail_le_wheel {K L : ℕ} (hL : 0 < L) (hK : 210*(L+1) ≤ K+1) :
    integerPrimeSquareTail K ≤ (48:ℝ)/210^2/L := by
  have hblocks (n : ℕ) : (∑ p ∈ range (210*n), integerPrimeSquareTerm K p) ≤
      ∑ j ∈ range n, wheel L j := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, sum_range_add, sum_range_succ (f := wheel L)]
      exact add_le_add ih (wheel_block hL hK n)
  apply le_of_tendsto' (summable_integerPrimeSquareTerm K).hasSum.tendsto_sum_nat
  intro n
  have hs : (range n).filter (fun j ↦ L < j) ⊆ Ioc L n := fun j hj ↦
    mem_Ioc.mpr ⟨(mem_filter.mp hj).2, (mem_range.mp (mem_filter.mp hj).1).le⟩
  calc
    _ ≤ ∑ p ∈ range (210*n), integerPrimeSquareTerm K p :=
      sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun p _ _ ↦ integerPrimeSquareTerm_nonneg _ _)
    _ ≤ _ := hblocks n
    _ = (48/210^2:ℝ) * (∑ j ∈ (range n).filter (fun j ↦ L < j), 1/(j:ℝ)^2) := by
      rw [mul_sum, sum_filter]; rfl
    _ ≤ (48/210^2:ℝ) * (1/(L:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ ↦ by positivity)).trans
        (sum_Ioc_one_div_sq_le L n hL)
    _ = _ := by ring

theorem integerPrimeSquareTail_wheel_bound :
    integerPrimeSquareTail 16383 ≤ (48:ℝ)/210^2/77 :=
  integerPrimeSquareTail_le_wheel (by decide) (by decide)

end GRHArticle.ProgressionFree
