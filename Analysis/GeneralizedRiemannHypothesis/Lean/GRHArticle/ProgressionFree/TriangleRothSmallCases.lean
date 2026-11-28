import GRHArticle.ProgressionFree.TriangleRothDeficiency

/-!
# The first two strict losses for exponent triangles

The exact interval maxima at lengths 5 and 9 force conflicting choices
at (4,0); those at 13 and 20 give the next conflict at (7,0).
-/

namespace GRHArticle.ProgressionFree

open Finset

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem rothNumberNat_eq_5 : rothNumberNat 5 = 4 := by
  apply le_antisymm
  · exact rothNumberNat_le_of_branchCheck 5 4 (by decide +kernel)
  · apply ThreeAPFree.le_rothNumberNat {0,1,3,4} <;> decide

theorem mem_interval_maximum_5 (B : Finset ℕ) (hs : B ⊆ range 5)
    (hf : ThreeAPFree (B : Set ℕ)) (he : B.card = rothNumberNat 5) : 0 ∈ B :=
  mem_of_interval_maximum (M := 4) (by decide +kernel) (by decide) hs hf (he.trans rothNumberNat_eq_5)

theorem rothNumberNat_eq_9 : rothNumberNat 9 = 5 := by
  apply le_antisymm
  · exact rothNumberNat_le_of_branchCheck 9 5 (by decide +kernel)
  · apply ThreeAPFree.le_rothNumberNat {0,1,3,7,8} <;> decide

theorem notMem_interval_maximum_9 (B : Finset ℕ) (hs : B ⊆ range 9)
    (hf : ThreeAPFree (B : Set ℕ)) (he : B.card = rothNumberNat 9) : 4 ∉ B :=
  notMem_of_interval_maximum (M := 5) (by decide +kernel) hs hf (he.trans rothNumberNat_eq_9)

theorem rothNumberNat_eq_13 : rothNumberNat 13 = 7 := by
  apply le_antisymm
  · exact rothNumberNat_le_of_branchCheck 13 7 (by decide +kernel)
  · apply ThreeAPFree.le_rothNumberNat {0,1,3,4,9,10,12} <;> decide

theorem mem_interval_maximum_13 (B : Finset ℕ) (hs : B ⊆ range 13)
    (hf : ThreeAPFree (B : Set ℕ)) (he : B.card = rothNumberNat 13) : 0 ∈ B :=
  mem_of_interval_maximum (M := 7) (by decide +kernel) (by decide) hs hf (he.trans rothNumberNat_eq_13)

theorem rothNumberNat_eq_20 : rothNumberNat 20 = 9 := by
  apply le_antisymm
  · exact rothNumberNat_le_of_branchCheck 20 9 (by decide +kernel)
  · apply ThreeAPFree.le_rothNumberNat {0,1,5,6,8,13,14,17,19} <;> decide

theorem notMem_interval_maximum_20 (B : Finset ℕ) (hs : B ⊆ range 20)
    (hf : ThreeAPFree (B : Set ℕ)) (he : B.card = rothNumberNat 20) : 7 ∉ B :=
  notMem_of_interval_maximum (M := 9) (by decide +kernel) hs hf (he.trans rothNumberNat_eq_20)

theorem triangleRothLoss_nine : TriangleRothLoss 9 1 :=
  TriangleRothLoss.succ_of_conflict (K := 0) (h := 0) (i := 4) (j := 0)
    (fun _ _ ↦ Nat.zero_le _) (by decide) (by decide) (by decide)
    mem_interval_maximum_5 notMem_interval_maximum_9

theorem triangleRothLoss_twenty : TriangleRothLoss 20 2 :=
  triangleRothLoss_nine.succ_of_conflict (i := 7) (j := 0) (by decide) (by decide) (by decide)
    mem_interval_maximum_13 notMem_interval_maximum_20

end GRHArticle.ProgressionFree
