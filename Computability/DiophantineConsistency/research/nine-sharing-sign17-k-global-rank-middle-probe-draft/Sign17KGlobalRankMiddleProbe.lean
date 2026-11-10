import DiophantineConsistency.Sign17KWeightUnion942

/-! SOURCE-ONLY: middle 64 global nonzero and adjacency cases. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KGlobalRankMiddleProbe

def nonzeroIndex (i : Fin 64) : Fin 941 := (Fin.natAdd 448 i).castAdd 429

def adjacentIndex (i : Fin 64) : Fin 940 := (Fin.natAdd 448 i).castAdd 428

theorem middle_nonzero (i : Fin 64) :
    Sign17KWeightUnion942.indices (nonzeroIndex i).succ ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem middle_adjacent (i : Fin 64) :
    Sign17KWeightUnion942.weights (adjacentIndex i).succ.succ <
      Sign17KWeightUnion942.weights (adjacentIndex i).castSucc.succ := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KGlobalRankMiddleProbe
#print axioms DiophantineConsistency.Sign17KGlobalRankMiddleProbe.middle_nonzero
#print axioms DiophantineConsistency.Sign17KGlobalRankMiddleProbe.middle_adjacent
