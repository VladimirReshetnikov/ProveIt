import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: one candidate weight checked against the actual Lean tile. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileSample
open WangTiles942

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem weight_start : selectorWeight (tile (0 : Fin 942)) = 34876427265 := by
  decide +kernel

end DiophantineConsistency.Sign17KTileSample
#print axioms DiophantineConsistency.Sign17KTileSample.weight_start
