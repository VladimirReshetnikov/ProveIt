import DiophantineConsistency.Sign17KWeightAggregateProbe
import DiophantineConsistency.Sign17KWeightAggregateBatch01
import DiophantineConsistency.Sign17KWeightAppend

/-! SOURCE-ONLY: combine two checked finite weight certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightUnion96
open WangTiles942

def indices : Fin 96 → Fin 942 := Fin.append
  Sign17KWeightAggregateProbe.indices Sign17KWeightAggregateBatch01.indices

def weights : Fin 96 → ℕ := Fin.append
  Sign17KWeightAggregateProbe.weights Sign17KWeightAggregateBatch01.weights

theorem all_weights (i : Fin 96) :
    selectorWeight (tile (indices i)) = weights i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    Sign17KWeightAggregateProbe.indices Sign17KWeightAggregateBatch01.indices
    Sign17KWeightAggregateProbe.weights Sign17KWeightAggregateBatch01.weights
    Sign17KWeightAggregateProbe.all_weights Sign17KWeightAggregateBatch01.all_weights i

end DiophantineConsistency.Sign17KWeightUnion96
#print axioms DiophantineConsistency.Sign17KWeightUnion96.all_weights
