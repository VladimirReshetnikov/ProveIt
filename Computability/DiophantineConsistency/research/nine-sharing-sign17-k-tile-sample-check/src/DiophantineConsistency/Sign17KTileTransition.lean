import DiophantineConsistency.Sign17KTileTail

/-! SOURCE-ONLY: one candidate weight checked against the actual Lean tile. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileSample
open WangTiles942

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem weight_transition : selectorWeight (tile (126 : Fin 942)) = 61773448193 := by
  decide +kernel

end DiophantineConsistency.Sign17KTileSample
#print axioms DiophantineConsistency.Sign17KTileSample.weight_transition
