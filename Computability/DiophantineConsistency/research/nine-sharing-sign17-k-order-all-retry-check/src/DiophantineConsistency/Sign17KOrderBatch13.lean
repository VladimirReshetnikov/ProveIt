import DiophantineConsistency.Sign17KWeightAggregateBatch13

/-! SOURCE-ONLY: within-block numeric ordering and nonzero index check. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KOrderBatch13
open WangTiles942 Sign17KWeightAggregateBatch13

theorem indices_ne_zero (i : Fin 64) : indices i ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem adjacent (i : Fin 63) : weights i.succ < weights i.castSucc := by
  fin_cases i <;> decide +kernel

theorem actual_adjacent (i : Fin 63) :
    selectorWeight (tile (indices i.succ)) <
      selectorWeight (tile (indices i.castSucc)) := by
  rw [all_weights, all_weights]
  exact adjacent i

end DiophantineConsistency.Sign17KOrderBatch13
#print axioms DiophantineConsistency.Sign17KOrderBatch13.indices_ne_zero
#print axioms DiophantineConsistency.Sign17KOrderBatch13.adjacent
#print axioms DiophantineConsistency.Sign17KOrderBatch13.actual_adjacent
