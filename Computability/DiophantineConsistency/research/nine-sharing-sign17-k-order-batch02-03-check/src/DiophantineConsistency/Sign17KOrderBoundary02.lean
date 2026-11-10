import DiophantineConsistency.Sign17KOrderBatch02
import DiophantineConsistency.Sign17KOrderBatch03

/-! SOURCE-ONLY: numeric and actual comparison at the adjacent-block boundary. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KOrderBoundary02
open WangTiles942

theorem boundary : Sign17KWeightAggregateBatch03.weights 0 <
    Sign17KWeightAggregateBatch02.weights 63 := by
  decide +kernel

theorem actual_boundary :
    selectorWeight (tile (Sign17KWeightAggregateBatch03.indices 0)) <
      selectorWeight (tile (Sign17KWeightAggregateBatch02.indices 63)) := by
  rw [Sign17KWeightAggregateBatch03.all_weights, Sign17KWeightAggregateBatch02.all_weights]
  exact boundary

end DiophantineConsistency.Sign17KOrderBoundary02
#print axioms DiophantineConsistency.Sign17KOrderBoundary02.boundary
#print axioms DiophantineConsistency.Sign17KOrderBoundary02.actual_boundary
