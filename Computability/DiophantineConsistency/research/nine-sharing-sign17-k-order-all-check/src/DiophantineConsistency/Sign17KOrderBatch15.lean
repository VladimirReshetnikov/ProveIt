import DiophantineConsistency.Sign17KWeightAggregateBatch15

/-! SOURCE-ONLY: within-block numeric ordering and nonzero index check. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KOrderBatch15
open WangTiles942 Sign17KWeightAggregateBatch15

theorem indices_ne_zero (i : Fin 14) : indices i ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem adjacent (i : Fin 13) : weights i.succ < weights i.castSucc := by
  fin_cases i <;> decide +kernel

theorem actual_adjacent (i : Fin 13) :
    selectorWeight (tile (indices i.succ)) <
      selectorWeight (tile (indices i.castSucc)) := by
  rw [all_weights, all_weights]
  exact adjacent i

end DiophantineConsistency.Sign17KOrderBatch15
#print axioms DiophantineConsistency.Sign17KOrderBatch15.indices_ne_zero
#print axioms DiophantineConsistency.Sign17KOrderBatch15.adjacent
#print axioms DiophantineConsistency.Sign17KOrderBatch15.actual_adjacent
