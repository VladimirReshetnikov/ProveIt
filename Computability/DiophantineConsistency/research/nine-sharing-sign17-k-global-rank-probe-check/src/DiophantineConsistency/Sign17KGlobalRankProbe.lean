import DiophantineConsistency.Sign17KWeightUnion942

/-! SOURCE-ONLY: first 16 global nonzero and adjacent numeric cases. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KGlobalRankProbe

theorem start_index : Sign17KWeightUnion942.indices 0 = 0 := by decide +kernel

theorem first_nonzero (i : Fin 16) :
    Sign17KWeightUnion942.indices (i.castAdd 925).succ ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem first_adjacent (i : Fin 16) :
    Sign17KWeightUnion942.weights (i.castAdd 924).succ.succ <
      Sign17KWeightUnion942.weights (i.castAdd 924).castSucc.succ := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KGlobalRankProbe
#print axioms DiophantineConsistency.Sign17KGlobalRankProbe.start_index
#print axioms DiophantineConsistency.Sign17KGlobalRankProbe.first_nonzero
#print axioms DiophantineConsistency.Sign17KGlobalRankProbe.first_adjacent
