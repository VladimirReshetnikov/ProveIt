import DiophantineConsistency.ArithmeticWangTableChunkBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace DiophantineConsistency.ArithmeticWangTable
open DiophantineConsistency.WangTiles942
theorem rows_goodC_chunk03 : ∀ row ∈ (orderedRows.drop 96).take 32, GoodC row.2 := by decide +kernel
#print axioms DiophantineConsistency.ArithmeticWangTable.rows_goodC_chunk03
end DiophantineConsistency.ArithmeticWangTable
