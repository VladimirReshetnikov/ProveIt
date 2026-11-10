import DiophantineConsistency.Sign17KTileCoeffUnion864
import DiophantineConsistency.Sign17KTileCoefficients14
import DiophantineConsistency.Sign17KTileCoefficients15
import DiophantineConsistency.Sign17KWeightUnion942

/-! SOURCE-ONLY: append two literal coefficient certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoeffUnion942

def literal928 : Fin 928 → ℕ := Fin.append
  Sign17KTileCoeffUnion864.literal Sign17KTileCoefficients14.literal

def literal : Fin 942 → ℕ := Fin.append literal928
  Sign17KTileCoefficients15.literal

theorem doubled_weights928 (i : Fin 928) :
    2 * Sign17KWeightUnion942.weights928 i = literal928 i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion864.weights Sign17KWeightAggregateBatch14.weights
    Sign17KTileCoeffUnion864.literal Sign17KTileCoefficients14.literal
    Sign17KTileCoeffUnion864.doubled_weights Sign17KTileCoefficients14.doubled_weights i

theorem doubled_weights (i : Fin 942) :
    2 * Sign17KWeightUnion942.weights i = literal i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion942.weights928 Sign17KWeightAggregateBatch15.weights
    literal928 Sign17KTileCoefficients15.literal
    doubled_weights928 Sign17KTileCoefficients15.doubled_weights i

end DiophantineConsistency.Sign17KTileCoeffUnion942
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion942.doubled_weights928
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion942.doubled_weights
