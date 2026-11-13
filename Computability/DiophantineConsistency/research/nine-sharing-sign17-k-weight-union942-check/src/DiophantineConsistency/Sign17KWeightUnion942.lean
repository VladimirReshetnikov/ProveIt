import DiophantineConsistency.Sign17KWeightUnion864
import DiophantineConsistency.Sign17KWeightAggregateBatch14
import DiophantineConsistency.Sign17KWeightAggregateBatch15

/-! SOURCE-ONLY: append two weight blocks to the prior union. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightUnion942
open WangTiles942

def indices928 : Fin 928 → Fin 942 := Fin.append
  Sign17KWeightUnion864.indices Sign17KWeightAggregateBatch14.indices

def weights928 : Fin 928 → ℕ := Fin.append
  Sign17KWeightUnion864.weights Sign17KWeightAggregateBatch14.weights

def indices : Fin 942 → Fin 942 := Fin.append indices928
  Sign17KWeightAggregateBatch15.indices

def weights : Fin 942 → ℕ := Fin.append weights928
  Sign17KWeightAggregateBatch15.weights

theorem all_weights928 (i : Fin 928) :
    selectorWeight (tile (indices928 i)) = weights928 i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    Sign17KWeightUnion864.indices Sign17KWeightAggregateBatch14.indices
    Sign17KWeightUnion864.weights Sign17KWeightAggregateBatch14.weights
    Sign17KWeightUnion864.all_weights Sign17KWeightAggregateBatch14.all_weights i

theorem all_weights (i : Fin 942) :
    selectorWeight (tile (indices i)) = weights i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    indices928 Sign17KWeightAggregateBatch15.indices
    weights928 Sign17KWeightAggregateBatch15.weights
    all_weights928 Sign17KWeightAggregateBatch15.all_weights i

end DiophantineConsistency.Sign17KWeightUnion942
#print axioms DiophantineConsistency.Sign17KWeightUnion942.all_weights928
#print axioms DiophantineConsistency.Sign17KWeightUnion942.all_weights
