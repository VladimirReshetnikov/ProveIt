import DiophantineConsistency.Sign17KWeightUnion736
import DiophantineConsistency.Sign17KWeightAggregateBatch12
import DiophantineConsistency.Sign17KWeightAggregateBatch13

/-! SOURCE-ONLY: append two weight blocks to the prior union. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightUnion864
open WangTiles942

def indices800 : Fin 800 → Fin 942 := Fin.append
  Sign17KWeightUnion736.indices Sign17KWeightAggregateBatch12.indices

def weights800 : Fin 800 → ℕ := Fin.append
  Sign17KWeightUnion736.weights Sign17KWeightAggregateBatch12.weights

def indices : Fin 864 → Fin 942 := Fin.append indices800
  Sign17KWeightAggregateBatch13.indices

def weights : Fin 864 → ℕ := Fin.append weights800
  Sign17KWeightAggregateBatch13.weights

theorem all_weights800 (i : Fin 800) :
    selectorWeight (tile (indices800 i)) = weights800 i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    Sign17KWeightUnion736.indices Sign17KWeightAggregateBatch12.indices
    Sign17KWeightUnion736.weights Sign17KWeightAggregateBatch12.weights
    Sign17KWeightUnion736.all_weights Sign17KWeightAggregateBatch12.all_weights i

theorem all_weights (i : Fin 864) :
    selectorWeight (tile (indices i)) = weights i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    indices800 Sign17KWeightAggregateBatch13.indices
    weights800 Sign17KWeightAggregateBatch13.weights
    all_weights800 Sign17KWeightAggregateBatch13.all_weights i

end DiophantineConsistency.Sign17KWeightUnion864
#print axioms DiophantineConsistency.Sign17KWeightUnion864.all_weights800
#print axioms DiophantineConsistency.Sign17KWeightUnion864.all_weights
