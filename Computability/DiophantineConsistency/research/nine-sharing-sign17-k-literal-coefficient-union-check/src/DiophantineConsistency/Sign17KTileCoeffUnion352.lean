import DiophantineConsistency.Sign17KTileCoeffUnion224
import DiophantineConsistency.Sign17KTileCoefficients04
import DiophantineConsistency.Sign17KTileCoefficients05
import DiophantineConsistency.Sign17KWeightUnion352

/-! SOURCE-ONLY: append two literal coefficient certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoeffUnion352

def literal288 : Fin 288 → ℕ := Fin.append
  Sign17KTileCoeffUnion224.literal Sign17KTileCoefficients04.literal

def literal : Fin 352 → ℕ := Fin.append literal288
  Sign17KTileCoefficients05.literal

theorem doubled_weights288 (i : Fin 288) :
    2 * Sign17KWeightUnion352.weights288 i = literal288 i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion224.weights Sign17KWeightAggregateBatch04.weights
    Sign17KTileCoeffUnion224.literal Sign17KTileCoefficients04.literal
    Sign17KTileCoeffUnion224.doubled_weights Sign17KTileCoefficients04.doubled_weights i

theorem doubled_weights (i : Fin 352) :
    2 * Sign17KWeightUnion352.weights i = literal i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion352.weights288 Sign17KWeightAggregateBatch05.weights
    literal288 Sign17KTileCoefficients05.literal
    doubled_weights288 Sign17KTileCoefficients05.doubled_weights i

end DiophantineConsistency.Sign17KTileCoeffUnion352
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion352.doubled_weights288
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion352.doubled_weights
