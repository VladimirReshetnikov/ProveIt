import DiophantineConsistency.Sign17KWeightUnion224
import DiophantineConsistency.Sign17KWeightAggregateBatch04
import DiophantineConsistency.Sign17KWeightAggregateBatch05

/-! SOURCE-ONLY: append two weight blocks to the prior union. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightUnion352
open WangTiles942

def indices288 : Fin 288 → Fin 942 := Fin.append
  Sign17KWeightUnion224.indices Sign17KWeightAggregateBatch04.indices

def weights288 : Fin 288 → ℕ := Fin.append
  Sign17KWeightUnion224.weights Sign17KWeightAggregateBatch04.weights

def indices : Fin 352 → Fin 942 := Fin.append indices288
  Sign17KWeightAggregateBatch05.indices

def weights : Fin 352 → ℕ := Fin.append weights288
  Sign17KWeightAggregateBatch05.weights

theorem all_weights288 (i : Fin 288) :
    selectorWeight (tile (indices288 i)) = weights288 i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    Sign17KWeightUnion224.indices Sign17KWeightAggregateBatch04.indices
    Sign17KWeightUnion224.weights Sign17KWeightAggregateBatch04.weights
    Sign17KWeightUnion224.all_weights Sign17KWeightAggregateBatch04.all_weights i

theorem all_weights (i : Fin 352) :
    selectorWeight (tile (indices i)) = weights i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    indices288 Sign17KWeightAggregateBatch05.indices
    weights288 Sign17KWeightAggregateBatch05.weights
    all_weights288 Sign17KWeightAggregateBatch05.all_weights i

end DiophantineConsistency.Sign17KWeightUnion352
#print axioms DiophantineConsistency.Sign17KWeightUnion352.all_weights288
#print axioms DiophantineConsistency.Sign17KWeightUnion352.all_weights
