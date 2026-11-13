import DiophantineConsistency.Sign17KTileCoeffUnion96
import DiophantineConsistency.Sign17KTileCoefficients02
import DiophantineConsistency.Sign17KTileCoefficients03
import DiophantineConsistency.Sign17KWeightUnion224

/-! SOURCE-ONLY: append two literal coefficient certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoeffUnion224

def literal160 : Fin 160 → ℕ := Fin.append
  Sign17KTileCoeffUnion96.literal Sign17KTileCoefficients02.literal

def literal : Fin 224 → ℕ := Fin.append literal160
  Sign17KTileCoefficients03.literal

theorem doubled_weights160 (i : Fin 160) :
    2 * Sign17KWeightUnion224.weights160 i = literal160 i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion96.weights Sign17KWeightAggregateBatch02.weights
    Sign17KTileCoeffUnion96.literal Sign17KTileCoefficients02.literal
    Sign17KTileCoeffUnion96.doubled_weights Sign17KTileCoefficients02.doubled_weights i

theorem doubled_weights (i : Fin 224) :
    2 * Sign17KWeightUnion224.weights i = literal i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion224.weights160 Sign17KWeightAggregateBatch03.weights
    literal160 Sign17KTileCoefficients03.literal
    doubled_weights160 Sign17KTileCoefficients03.doubled_weights i

end DiophantineConsistency.Sign17KTileCoeffUnion224
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion224.doubled_weights160
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion224.doubled_weights
