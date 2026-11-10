import DiophantineConsistency.Sign17KTileCoeffUnion480
import DiophantineConsistency.Sign17KTileCoefficients08
import DiophantineConsistency.Sign17KTileCoefficients09
import DiophantineConsistency.Sign17KWeightUnion608

/-! SOURCE-ONLY: append two literal coefficient certificates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoeffUnion608

def literal544 : Fin 544 → ℕ := Fin.append
  Sign17KTileCoeffUnion480.literal Sign17KTileCoefficients08.literal

def literal : Fin 608 → ℕ := Fin.append literal544
  Sign17KTileCoefficients09.literal

theorem doubled_weights544 (i : Fin 544) :
    2 * Sign17KWeightUnion608.weights544 i = literal544 i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion480.weights Sign17KWeightAggregateBatch08.weights
    Sign17KTileCoeffUnion480.literal Sign17KTileCoefficients08.literal
    Sign17KTileCoeffUnion480.doubled_weights Sign17KTileCoefficients08.doubled_weights i

theorem doubled_weights (i : Fin 608) :
    2 * Sign17KWeightUnion608.weights i = literal i := by
  exact Sign17KWeightAppend.append_certificates (fun x => 2 * x)
    Sign17KWeightUnion608.weights544 Sign17KWeightAggregateBatch09.weights
    literal544 Sign17KTileCoefficients09.literal
    doubled_weights544 Sign17KTileCoefficients09.doubled_weights i

end DiophantineConsistency.Sign17KTileCoeffUnion608
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion608.doubled_weights544
#print axioms DiophantineConsistency.Sign17KTileCoeffUnion608.doubled_weights
