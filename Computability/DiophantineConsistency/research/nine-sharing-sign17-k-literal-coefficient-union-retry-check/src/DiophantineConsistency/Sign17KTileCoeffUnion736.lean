import DiophantineConsistency.Sign17KTileCoeffUnion608
import DiophantineConsistency.Sign17KTileCoefficients10
import DiophantineConsistency.Sign17KTileCoefficients11
import DiophantineConsistency.Sign17KWeightUnion736

/-! SOURCE-ONLY: append two literal coefficient certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoeffUnion736

def literal672 : Fin 672 → ℕ := Fin.append
  Sign17KTileCoeffUnion608.literal Sign17KTileCoefficients10.literal

def literal : Fin 736 → ℕ := Fin.append literal672
  Sign17KTileCoefficients11.literal

theorem doubled_weights672 (i : Fin 672) :
    2 * Sign17KWeightUnion736.weights672 i = literal672 i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion608.weights Sign17KWeightAggregateBatch10.weights
    Sign17KTileCoeffUnion608.literal Sign17KTileCoefficients10.literal
    Sign17KTileCoeffUnion608.doubled_weights Sign17KTileCoefficients10.doubled_weights i

theorem doubled_weights (i : Fin 736) :
    2 * Sign17KWeightUnion736.weights i = literal i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion736.weights672 Sign17KWeightAggregateBatch11.weights
    literal672 Sign17KTileCoefficients11.literal
    doubled_weights672 Sign17KTileCoefficients11.doubled_weights i

end DiophantineConsistency.Sign17KTileCoeffUnion736
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion736.doubled_weights672
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion736.doubled_weights
