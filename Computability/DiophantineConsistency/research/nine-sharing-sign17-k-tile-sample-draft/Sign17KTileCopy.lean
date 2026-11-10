import DiophantineConsistency.Sign17KTileTransition

/-! SOURCE-ONLY: one candidate weight checked against the actual Lean tile. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileSample
open WangTiles942

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem weight_copy : selectorWeight (tile (432 : Fin 942)) = 14877880222721 := by
  decide +kernel

end DiophantineConsistency.Sign17KTileSample
#print axioms DiophantineConsistency.Sign17KTileSample.weight_copy
