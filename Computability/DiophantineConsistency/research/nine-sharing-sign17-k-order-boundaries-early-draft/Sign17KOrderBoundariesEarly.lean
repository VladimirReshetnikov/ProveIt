import DiophantineConsistency.Sign17KWeightUnion224

/-! SOURCE-ONLY: boundary comparisons at witness rows 31/32 and 95/96. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KOrderBoundariesEarly
open WangTiles942

theorem boundary31_32 : Sign17KWeightAggregateBatch01.weights 0 <
    Sign17KWeightAggregateProbe.weights 31 := by decide +kernel

theorem boundary95_96 : Sign17KWeightAggregateBatch02.weights 0 <
    Sign17KWeightAggregateBatch01.weights 63 := by decide +kernel

theorem actual_boundary31_32 :
    selectorWeight (tile (Sign17KWeightAggregateBatch01.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateProbe.indices 31)) := by
  rw [Sign17KWeightAggregateBatch01.all_weights, Sign17KWeightAggregateProbe.all_weights]
  exact boundary31_32

theorem actual_boundary95_96 :
    selectorWeight (tile (Sign17KWeightAggregateBatch02.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch01.indices 63)) := by
  rw [Sign17KWeightAggregateBatch02.all_weights, Sign17KWeightAggregateBatch01.all_weights]
  exact boundary95_96

end DiophantineConsistency.Sign17KOrderBoundariesEarly
#print axioms DiophantineConsistency.Sign17KOrderBoundariesEarly.actual_boundary31_32
#print axioms DiophantineConsistency.Sign17KOrderBoundariesEarly.actual_boundary95_96
