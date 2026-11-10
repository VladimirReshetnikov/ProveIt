import DiophantineConsistency.Sign17KWeightUnion942

/-! SOURCE-ONLY: global candidate cases at offset 448. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KGlobalChunk07

def nonzeroIndex (i : Fin 64) : Fin 941 := (Fin.natAdd 448 i).castAdd 429

def adjacentIndex (i : Fin 64) : Fin 940 := (Fin.natAdd 448 i).castAdd 428

theorem nonzero (i : Fin 64) :
    Sign17KWeightUnion942.indices (nonzeroIndex i).succ ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem adjacent (i : Fin 64) :
    Sign17KWeightUnion942.weights (adjacentIndex i).succ.succ <
      Sign17KWeightUnion942.weights (adjacentIndex i).castSucc.succ := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KGlobalChunk07
#print axioms DiophantineConsistency.Sign17KGlobalChunk07.nonzero
#print axioms DiophantineConsistency.Sign17KGlobalChunk07.adjacent
