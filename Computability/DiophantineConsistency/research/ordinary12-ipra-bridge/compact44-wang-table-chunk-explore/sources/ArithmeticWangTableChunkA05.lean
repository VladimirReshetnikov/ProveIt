import DiophantineConsistency.ArithmeticWangTableChunkBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace DiophantineConsistency.ArithmeticWangTable
open DiophantineConsistency.WangTiles942
theorem rows_goodA_chunk05 : ∀ row ∈ (orderedRows.drop 160).take 32, GoodA row.2 := by decide +kernel
#print axioms DiophantineConsistency.ArithmeticWangTable.rows_goodA_chunk05
end DiophantineConsistency.ArithmeticWangTable
