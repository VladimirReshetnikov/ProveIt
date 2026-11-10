import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: one uniformly quantified K weight batch, not a rank theorem. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KWeightAggregateBatch15
open WangTiles942

def indices : Fin 14 → Fin 942 := ![33, 31, 29, 27, 26, 23, 18, 17, 16, 14, 13, 11, 9, 433]
def weights : Fin 14 → ℕ := ![9136129, 8610817, 8085505, 7559169, 7297025, 6509569, 5195777, 4932609, 4670465, 4148225, 3885057, 3359745, 2833409, 1025]

theorem all_weights (i : Fin 14) : selectorWeight (tile (indices i)) = weights i := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KWeightAggregateBatch15
#print axioms DiophantineConsistency.Sign17KWeightAggregateBatch15.all_weights
