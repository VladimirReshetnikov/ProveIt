import DiophantineConsistency.Sign17KWeightUnion480
import DiophantineConsistency.Sign17KWeightAggregateBatch08
import DiophantineConsistency.Sign17KWeightAggregateBatch09

/-! SOURCE-ONLY: append two weight blocks to the prior union. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightUnion608
open WangTiles942

def indices544 : Fin 544 → Fin 942 := Fin.append
  Sign17KWeightUnion480.indices Sign17KWeightAggregateBatch08.indices

def weights544 : Fin 544 → ℕ := Fin.append
  Sign17KWeightUnion480.weights Sign17KWeightAggregateBatch08.weights

def indices : Fin 608 → Fin 942 := Fin.append indices544
  Sign17KWeightAggregateBatch09.indices

def weights : Fin 608 → ℕ := Fin.append weights544
  Sign17KWeightAggregateBatch09.weights

theorem all_weights544 (i : Fin 544) :
    selectorWeight (tile (indices544 i)) = weights544 i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    Sign17KWeightUnion480.indices Sign17KWeightAggregateBatch08.indices
    Sign17KWeightUnion480.weights Sign17KWeightAggregateBatch08.weights
    Sign17KWeightUnion480.all_weights Sign17KWeightAggregateBatch08.all_weights i

theorem all_weights (i : Fin 608) :
    selectorWeight (tile (indices i)) = weights i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    indices544 Sign17KWeightAggregateBatch09.indices
    weights544 Sign17KWeightAggregateBatch09.weights
    all_weights544 Sign17KWeightAggregateBatch09.all_weights i

end DiophantineConsistency.Sign17KWeightUnion608
#print axioms DiophantineConsistency.Sign17KWeightUnion608.all_weights544
#print axioms DiophantineConsistency.Sign17KWeightUnion608.all_weights
