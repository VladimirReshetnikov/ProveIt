import DiophantineConsistency.Sign17KTileCoeffUnion352
import DiophantineConsistency.Sign17KTileCoefficients06
import DiophantineConsistency.Sign17KTileCoefficients07
import DiophantineConsistency.Sign17KWeightUnion480

/-! SOURCE-ONLY: append two literal coefficient certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoeffUnion480

def literal416 : Fin 416 → ℕ := Fin.append
  Sign17KTileCoeffUnion352.literal Sign17KTileCoefficients06.literal

def literal : Fin 480 → ℕ := Fin.append literal416
  Sign17KTileCoefficients07.literal

theorem doubled_weights416 (i : Fin 416) :
    2 * Sign17KWeightUnion480.weights416 i = literal416 i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion352.weights Sign17KWeightAggregateBatch06.weights
    Sign17KTileCoeffUnion352.literal Sign17KTileCoefficients06.literal
    Sign17KTileCoeffUnion352.doubled_weights Sign17KTileCoefficients06.doubled_weights i

theorem doubled_weights (i : Fin 480) :
    2 * Sign17KWeightUnion480.weights i = literal i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion480.weights416 Sign17KWeightAggregateBatch07.weights
    literal416 Sign17KTileCoefficients07.literal
    doubled_weights416 Sign17KTileCoefficients07.doubled_weights i

end DiophantineConsistency.Sign17KTileCoeffUnion480
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion480.doubled_weights416
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion480.doubled_weights
