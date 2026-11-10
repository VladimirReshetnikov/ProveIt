import DiophantineConsistency.Sign17LinesRails

/-! SOURCE ONLY. Reconstruct the target-list order from the decimal actions. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17LinesTargetOrder

open Sign17LinesRails

def lineTargetList (d : Bool) : List ℕ :=
  (WangTiles942.targetsFrom d lineActions).sort (· ≤ ·)

theorem targetList_sorted (d : Bool) :
    (WangTiles942.targetList d).Pairwise (· ≤ ·) := by
  cases d <;> decide +kernel

theorem targetList_from_lines (d : Bool) :
    WangTiles942.targetList d = lineTargetList d := by
  unfold lineTargetList
  rw [← target_set_from_lines]
  change WangTiles942.targetList d = (WangTiles942.targetList d).toFinset.sort (· ≤ ·)
  exact ((List.toFinset_sort (· ≤ ·) (WangTiles942.targetList_nodup d)).2
    (targetList_sorted d)).symm

end DiophantineConsistency.Sign17LinesTargetOrder
#print axioms DiophantineConsistency.Sign17LinesTargetOrder.targetList_from_lines
