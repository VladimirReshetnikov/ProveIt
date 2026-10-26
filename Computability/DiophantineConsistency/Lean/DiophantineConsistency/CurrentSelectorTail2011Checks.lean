import DiophantineConsistency.CurrentSelectorTail2011

/-!
# Checks of the exact current physical coefficient tail

The table, rank and coefficient sums are the literal current ones. The final
source bound still takes Boolean digits and the physical suffix restriction
as hypotheses; it does not claim the complete native decoding theorem.
-/

namespace DiophantineConsistency.CurrentSelectorTail2011Checks

open WangTiles942 CurrentSelectorTail2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

example : tile 866 = ⟨0,1,221,45⟩ := cutoff_tile

example : selectorWeight (tile 866) = 1575850607617 :=
  (congrArg selectorWeight cutoff_tile).trans cutoff_weight

example : physicalMap 866 = (459 : Fin 942) := by
  apply Fin.ext
  exact cutoff_position

example : physicalEquiv.symm 459 = 866 := by
  apply physicalEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  exact cutoff_position.symm

example (i : Fin 942) :
    459 ≤ physicalPosition i ↔ i ≠ 0 ∧ (tile i).south ≤ 45 :=
  tail_position_iff i

example : ((orderedRows.drop 1).map (fun row => lowCount row.2)).sum = 483 :=
  selected_count

example : ((orderedRows.drop 1).map (fun row => lowMass row.2)).sum = 51317956228579 :=
  selected_mass

example : (∑ e : CurrentKernel2011.Entry,
    if 459 ≤ CurrentKernel2011.position e then 2 * CurrentKernel2011.weight e else 0) =
      137820284543942 := tailMass_eq

example : 137820284543942 + 1024 + 3 + 57 < 2^47 := by
  have h := early_reset_numeric
  exact h

example (a : CurrentKernel2011.Entry → ℕ)
    (ha : ∀ e, a e ≤ 1)
    (hz : ∀ e, CurrentKernel2011.position e < 459 → a e = 0)
    (units temporal incoming : ℕ) (hu : units ≤ 3) (ht : temporal ≤ 2^10)
    (hk : incoming ≤ 57) :
    (∑ e, 2 * CurrentKernel2011.weight e * a e) + units + temporal + incoming <
      CurrentKernel2011.radix := early_reset_bound a ha hz units temporal incoming hu ht hk

#print axioms cutoff_tile
#print axioms cutoff_weight
#print axioms weight_le_cutoff_iff
#print axioms selected_count
#print axioms selected_mass
#print axioms cutoff_position
#print axioms tail_position_iff
#print axioms tailMass_eq
#print axioms tail_source_bound
#print axioms early_reset_numeric
#print axioms early_reset_bound

end DiophantineConsistency.CurrentSelectorTail2011Checks
