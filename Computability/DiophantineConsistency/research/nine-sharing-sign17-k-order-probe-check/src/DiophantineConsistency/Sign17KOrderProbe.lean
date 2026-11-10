import DiophantineConsistency.Sign17KWeightAggregateProbe

/-! SOURCE-ONLY: nonzero and within-block order for non-Start positions 1–31. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KOrderProbe
open WangTiles942 Sign17KWeightAggregateProbe

theorem start_index : indices 0 = 0 := by decide +kernel

theorem nonstart_indices_ne_zero (i : Fin 31) : indices i.succ ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem nonstart_adjacent (i : Fin 30) :
    weights i.succ.succ < weights i.castSucc.succ := by
  fin_cases i <;> decide +kernel

theorem actual_nonstart_adjacent (i : Fin 30) :
    selectorWeight (tile (indices i.succ.succ)) <
      selectorWeight (tile (indices i.castSucc.succ)) := by
  rw [all_weights, all_weights]
  exact nonstart_adjacent i

end DiophantineConsistency.Sign17KOrderProbe
#print axioms DiophantineConsistency.Sign17KOrderProbe.start_index
#print axioms DiophantineConsistency.Sign17KOrderProbe.nonstart_indices_ne_zero
#print axioms DiophantineConsistency.Sign17KOrderProbe.nonstart_adjacent
#print axioms DiophantineConsistency.Sign17KOrderProbe.actual_nonstart_adjacent
