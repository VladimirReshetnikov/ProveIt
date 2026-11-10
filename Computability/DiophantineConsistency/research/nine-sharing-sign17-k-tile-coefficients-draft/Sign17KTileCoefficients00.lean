import DiophantineConsistency.Sign17KWeightAggregateProbe

/-! SOURCE-ONLY: doubled in-Lean weights versus this finite literal block. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoefficients00

def literal : Fin 32 → ℕ := ![69752854530, 30099357829122, 30099357304834, 30099131336706, 30099130812418, 30031177328642, 30031177322498, 30031177320450, 30030908893186, 30030908887042, 30030908884994, 30030640457730, 30030640451586, 30030640449538, 29962189934594, 29893470457858, 29824750981122, 29755760445442, 29755534370818, 29687040444418, 29686814369794, 29618095415298, 29549375414274, 29480656459778, 29411936458754, 29343217504258, 29274497503234, 29205778548738, 29137058547714, 29068339593218, 28999619592194, 28997740660738]

theorem doubled_weights (i : Fin 32) :
    2 * Sign17KWeightAggregateProbe.weights i = literal i := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KTileCoefficients00
#print axioms DiophantineConsistency.Sign17KTileCoefficients00.doubled_weights
