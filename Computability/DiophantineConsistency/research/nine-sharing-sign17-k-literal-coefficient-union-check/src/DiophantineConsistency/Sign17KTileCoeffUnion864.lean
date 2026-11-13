import DiophantineConsistency.Sign17KTileCoeffUnion736
import DiophantineConsistency.Sign17KTileCoefficients12
import DiophantineConsistency.Sign17KTileCoefficients13
import DiophantineConsistency.Sign17KWeightUnion864

/-! SOURCE-ONLY: append two literal coefficient certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoeffUnion864

def literal800 : Fin 800 → ℕ := Fin.append
  Sign17KTileCoeffUnion736.literal Sign17KTileCoefficients12.literal

def literal : Fin 864 → ℕ := Fin.append literal800
  Sign17KTileCoefficients13.literal

theorem doubled_weights800 (i : Fin 800) :
    2 * Sign17KWeightUnion864.weights800 i = literal800 i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion736.weights Sign17KWeightAggregateBatch12.weights
    Sign17KTileCoeffUnion736.literal Sign17KTileCoefficients12.literal
    Sign17KTileCoeffUnion736.doubled_weights Sign17KTileCoefficients12.doubled_weights i

theorem doubled_weights (i : Fin 864) :
    2 * Sign17KWeightUnion864.weights i = literal i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion864.weights800 Sign17KWeightAggregateBatch13.weights
    literal800 Sign17KTileCoefficients13.literal
    doubled_weights800 Sign17KTileCoefficients13.doubled_weights i

end DiophantineConsistency.Sign17KTileCoeffUnion864
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion864.doubled_weights800
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion864.doubled_weights
