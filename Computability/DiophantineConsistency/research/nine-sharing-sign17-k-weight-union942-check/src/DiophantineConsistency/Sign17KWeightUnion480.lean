import DiophantineConsistency.Sign17KWeightUnion352
import DiophantineConsistency.Sign17KWeightAggregateBatch06
import DiophantineConsistency.Sign17KWeightAggregateBatch07

/-! SOURCE-ONLY: append two weight blocks to the prior union. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightUnion480
open WangTiles942

def indices416 : Fin 416 → Fin 942 := Fin.append
  Sign17KWeightUnion352.indices Sign17KWeightAggregateBatch06.indices

def weights416 : Fin 416 → ℕ := Fin.append
  Sign17KWeightUnion352.weights Sign17KWeightAggregateBatch06.weights

def indices : Fin 480 → Fin 942 := Fin.append indices416
  Sign17KWeightAggregateBatch07.indices

def weights : Fin 480 → ℕ := Fin.append weights416
  Sign17KWeightAggregateBatch07.weights

theorem all_weights416 (i : Fin 416) :
    selectorWeight (tile (indices416 i)) = weights416 i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    Sign17KWeightUnion352.indices Sign17KWeightAggregateBatch06.indices
    Sign17KWeightUnion352.weights Sign17KWeightAggregateBatch06.weights
    Sign17KWeightUnion352.all_weights Sign17KWeightAggregateBatch06.all_weights i

theorem all_weights (i : Fin 480) :
    selectorWeight (tile (indices i)) = weights i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    indices416 Sign17KWeightAggregateBatch07.indices
    weights416 Sign17KWeightAggregateBatch07.weights
    all_weights416 Sign17KWeightAggregateBatch07.all_weights i

end DiophantineConsistency.Sign17KWeightUnion480
#print axioms DiophantineConsistency.Sign17KWeightUnion480.all_weights416
#print axioms DiophantineConsistency.Sign17KWeightUnion480.all_weights
