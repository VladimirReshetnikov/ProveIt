import DiophantineConsistency.Sign17KWeightAggregateBatch15

/-! SOURCE-ONLY: doubled in-Lean weights versus this finite literal block. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KTileCoefficients15

def literal : Fin 14 → ℕ := ![18272258, 17221634, 16171010, 15118338, 14594050, 13019138, 10391554, 9865218, 9340930, 8296450, 7770114, 6719490, 5666818, 2050]

theorem doubled_weights (i : Fin 14) :
    2 * Sign17KWeightAggregateBatch15.weights i = literal i := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KTileCoefficients15
#print axioms DiophantineConsistency.Sign17KTileCoefficients15.doubled_weights
