import DiophantineConsistency.Sign17KWeightUnion608
import DiophantineConsistency.Sign17KWeightAggregateBatch10
import DiophantineConsistency.Sign17KWeightAggregateBatch11

/-! SOURCE-ONLY: append two weight blocks to the prior union. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightUnion736
open WangTiles942

def indices672 : Fin 672 → Fin 942 := Fin.append
  Sign17KWeightUnion608.indices Sign17KWeightAggregateBatch10.indices

def weights672 : Fin 672 → ℕ := Fin.append
  Sign17KWeightUnion608.weights Sign17KWeightAggregateBatch10.weights

def indices : Fin 736 → Fin 942 := Fin.append indices672
  Sign17KWeightAggregateBatch11.indices

def weights : Fin 736 → ℕ := Fin.append weights672
  Sign17KWeightAggregateBatch11.weights

theorem all_weights672 (i : Fin 672) :
    selectorWeight (tile (indices672 i)) = weights672 i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    Sign17KWeightUnion608.indices Sign17KWeightAggregateBatch10.indices
    Sign17KWeightUnion608.weights Sign17KWeightAggregateBatch10.weights
    Sign17KWeightUnion608.all_weights Sign17KWeightAggregateBatch10.all_weights i

theorem all_weights (i : Fin 736) :
    selectorWeight (tile (indices i)) = weights i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    indices672 Sign17KWeightAggregateBatch11.indices
    weights672 Sign17KWeightAggregateBatch11.weights
    all_weights672 Sign17KWeightAggregateBatch11.all_weights i

end DiophantineConsistency.Sign17KWeightUnion736
#print axioms DiophantineConsistency.Sign17KWeightUnion736.all_weights672
#print axioms DiophantineConsistency.Sign17KWeightUnion736.all_weights
