import DiophantineConsistency.ArithmeticWangTableChunkBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace DiophantineConsistency.ArithmeticWangTable
open DiophantineConsistency.WangTiles942
theorem rows_goodB_chunk08 : ∀ row ∈ (orderedRows.drop 256).take 32, GoodB row.2 := by decide +kernel
#print axioms DiophantineConsistency.ArithmeticWangTable.rows_goodB_chunk08
end DiophantineConsistency.ArithmeticWangTable
