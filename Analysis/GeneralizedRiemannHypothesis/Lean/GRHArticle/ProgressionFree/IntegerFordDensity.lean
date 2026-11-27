import GRHArticle.ProgressionFree.IntegerFordBlocks
import GRHArticle.ProgressionFree.IntegerBlockGluing

/-!
# The integral-ratio upper density in Ford's construction

Arbitrarily large double blocks have precisely the same admissible
proportion. Separated windows give the lower bound for the supremum over
individual infinite sets.
-/

namespace GRHArticle.ProgressionFree

open Finset

private theorem countUpTo_coe_finset {B : Finset ℕ} {N : ℕ} (hB : B ⊆ Icc 1 N) :
    countUpTo (B : Set ℕ) N = B.card := by
  classical
  unfold countUpTo
  congr 1
  ext n
  simp only [mem_filter, Finset.mem_coe]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hB h, h⟩⟩

/-- The sharp proportion of the specified double block survives in the
upper-density supremum. -/
theorem integerUpperDensitySupremum_integral_ford :
    (271529:ℝ)/331776 ≤ integerUpperDensitySupremum true := by
  apply le_integerUpperDensitySupremum_of_arbitrarily_large_prefix
  intro ε hε N₀
  let t := N₀+1
  let N := 8640*(2304*t)
  let B := integerFordDoubleBlock t
  have hN : N₀ ≤ N := by dsimp [N,t]; omega
  have hB : B ⊆ Icc 1 N := fun _ hn ↦ mem_Icc.mpr (mem_integerFordDoubleBlock_bounds hn)
  have hcount : countUpTo (B : Set ℕ) N = 7068 * 2305 * t :=
    (countUpTo_coe_finset hB).trans (card_integerFordDoubleBlock t)
  have hpos : 0 < (t:ℝ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  refine ⟨N, hN, B, integerFordDoubleBlock_admissible t, ?_⟩
  apply (sub_le_self _ hε.le).trans
  rw [densityUpTo, hcount]
  dsimp only [N]
  push_cast
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8640) (mul_pos (by norm_num : (0:ℝ)<2304) hpos))).mpr
  linarith

end GRHArticle.ProgressionFree
