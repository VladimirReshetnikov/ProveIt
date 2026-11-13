import DiophantineConsistency.Sign17KWeightUnion96
import DiophantineConsistency.Sign17KWeightAggregateBatch02
import DiophantineConsistency.Sign17KWeightAggregateBatch03

/-! SOURCE-ONLY: append two checked weight blocks to the first Fin96 union. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightUnion224
open WangTiles942

def indices160 : Fin 160 → Fin 942 := Fin.append
  Sign17KWeightUnion96.indices Sign17KWeightAggregateBatch02.indices

def weights160 : Fin 160 → ℕ := Fin.append
  Sign17KWeightUnion96.weights Sign17KWeightAggregateBatch02.weights

def indices : Fin 224 → Fin 942 := Fin.append indices160
  Sign17KWeightAggregateBatch03.indices

def weights : Fin 224 → ℕ := Fin.append weights160
  Sign17KWeightAggregateBatch03.weights

theorem all_weights160 (i : Fin 160) :
    selectorWeight (tile (indices160 i)) = weights160 i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    Sign17KWeightUnion96.indices Sign17KWeightAggregateBatch02.indices
    Sign17KWeightUnion96.weights Sign17KWeightAggregateBatch02.weights
    Sign17KWeightUnion96.all_weights Sign17KWeightAggregateBatch02.all_weights i

theorem all_weights (i : Fin 224) :
    selectorWeight (tile (indices i)) = weights i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    indices160 Sign17KWeightAggregateBatch03.indices
    weights160 Sign17KWeightAggregateBatch03.weights
    all_weights160 Sign17KWeightAggregateBatch03.all_weights i

end DiophantineConsistency.Sign17KWeightUnion224
#print axioms DiophantineConsistency.Sign17KWeightUnion224.all_weights160
#print axioms DiophantineConsistency.Sign17KWeightUnion224.all_weights
