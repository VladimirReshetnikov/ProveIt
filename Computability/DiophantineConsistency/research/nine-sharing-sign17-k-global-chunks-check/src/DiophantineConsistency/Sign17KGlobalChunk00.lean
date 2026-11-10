import DiophantineConsistency.Sign17KWeightUnion942

/-! SOURCE-ONLY: global candidate cases at offset 0. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KGlobalChunk00

def nonzeroIndex (i : Fin 64) : Fin 941 := (Fin.natAdd 0 i).castAdd 877

def adjacentIndex (i : Fin 64) : Fin 940 := (Fin.natAdd 0 i).castAdd 876

theorem start_index : Sign17KWeightUnion942.indices 0 = 0 := by decide +kernel

theorem nonzero (i : Fin 64) :
    Sign17KWeightUnion942.indices (nonzeroIndex i).succ ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem adjacent (i : Fin 64) :
    Sign17KWeightUnion942.weights (adjacentIndex i).succ.succ <
      Sign17KWeightUnion942.weights (adjacentIndex i).castSucc.succ := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KGlobalChunk00
#print axioms DiophantineConsistency.Sign17KGlobalChunk00.start_index
#print axioms DiophantineConsistency.Sign17KGlobalChunk00.nonzero
#print axioms DiophantineConsistency.Sign17KGlobalChunk00.adjacent
