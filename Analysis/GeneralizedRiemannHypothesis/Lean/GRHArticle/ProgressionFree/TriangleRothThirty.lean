import GRHArticle.ProgressionFree.IntervalRothExtrema
import GRHArticle.ProgressionFree.TriangleRothSmallCases

/-!
# The three two-prime triangle losses

At length 30, the optimal row of length 26 must include zero and the
optimal column of length 30 must omit four. This adds a third loss to
the previous tip of length 20.
-/

namespace GRHArticle.ProgressionFree

open Finset

set_option maxRecDepth 30000
set_option maxHeartbeats 1500000

theorem rothNumberNat_eq_26 : rothNumberNat 26 = 11 := by
  apply le_antisymm
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)
  · apply ThreeAPFree.le_rothNumberNat {0,1,4,6,10,15,17,18,22,23,25} <;> decide

theorem rothNumberNat_eq_30 : rothNumberNat 30 = 12 := by
  apply le_antisymm
  · exact rothNumberNat_le_of_byteCheck (by decide +kernel)
  · apply ThreeAPFree.le_rothNumberNat {0,2,3,7,8,10,19,21,22,26,27,29} <;> decide

theorem mem_interval_maximum_26 (B : Finset ℕ) (hs : B ⊆ range 26)
    (hf : ThreeAPFree (B : Set ℕ)) (he : B.card = rothNumberNat 26) : 0 ∈ B :=
  zero_mem_interval_of_byteCheck (M := 11) (by decide) (by decide +kernel) hs hf
    (he.trans rothNumberNat_eq_26).symm.le

theorem notMem_interval_maximum_30 (B : Finset ℕ) (hs : B ⊆ range 30)
    (hf : ThreeAPFree (B : Set ℕ)) (he : B.card = rothNumberNat 30) : 4 ∉ B :=
  notMem_interval_of_byteCheck (M := 12) (by decide +kernel) hs hf
    (he.trans rothNumberNat_eq_30).symm.le

theorem triangleRothLoss_thirty : TriangleRothLoss 30 3 :=
  triangleRothLoss_twenty.succ_of_conflict (i := 4) (j := 0) (by decide) (by decide) (by decide)
    mem_interval_maximum_26 notMem_interval_maximum_30

/-- A finite set of exponent pairs loses one unit at each of lengths
9, 20 and 30, even if only axis-aligned progressions are forbidden. -/
theorem card_triangle_le_roth_rows_sub_penalty {L : ℕ} (A : Finset (ℕ × ℕ))
    (hL : ∀ x ∈ A, x.1+x.2<L)
    (hr : ∀ i : ℕ, ThreeAPFree {j : ℕ | (i,j) ∈ A})
    (hc : ∀ j : ℕ, ThreeAPFree {i : ℕ | (i,j) ∈ A}) :
    A.card + ((if 9 ≤ L then 1 else 0) + (if 20 ≤ L then 1 else 0) + (if 30 ≤ L then 1 else 0)) ≤
      ∑ i ∈ range L, rothNumberNat (L-i) := by
  apply TriangleRothLoss.card_le _ A hL ⟨hr,hc⟩
  by_cases h30 : 30 ≤ L
  · simpa [h30,show 9 ≤ L by omega,show 20 ≤ L by omega] using triangleRothLoss_thirty.mono_length h30
  by_cases h20 : 20 ≤ L
  · simpa [h30,h20,show 9 ≤ L by omega] using triangleRothLoss_twenty.mono_length h20
  by_cases h9 : 9 ≤ L
  · simpa [h30,h20,h9] using triangleRothLoss_nine.mono_length h9
  · simp only [if_neg h30,if_neg h20,if_neg h9, zero_add]
    exact fun _ _ ↦ Nat.zero_le _

end GRHArticle.ProgressionFree
