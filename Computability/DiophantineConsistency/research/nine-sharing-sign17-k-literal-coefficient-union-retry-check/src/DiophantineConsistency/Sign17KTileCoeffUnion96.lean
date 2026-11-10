import DiophantineConsistency.Sign17KTileCoefficients00
import DiophantineConsistency.Sign17KTileCoefficients01
import DiophantineConsistency.Sign17KWeightAppend
import DiophantineConsistency.Sign17KWeightUnion96

/-! SOURCE-ONLY: join first two literal coefficient certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoeffUnion96

def literal : Fin 96 → ℕ := Fin.append
  Sign17KTileCoefficients00.literal Sign17KTileCoefficients01.literal

theorem doubled_weights (i : Fin 96) :
    2 * Sign17KWeightUnion96.weights i = literal i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightAggregateProbe.weights Sign17KWeightAggregateBatch01.weights
    Sign17KTileCoefficients00.literal Sign17KTileCoefficients01.literal
    Sign17KTileCoefficients00.doubled_weights Sign17KTileCoefficients01.doubled_weights i

end DiophantineConsistency.Sign17KTileCoeffUnion96
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion96.doubled_weights
