import DiophantineConsistency.ArithmeticWangTableChunkCore
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace DiophantineConsistency.ArithmeticWangTable
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open WangTiles942
/-- One finite chunk of the original GoodA predicate. -/
theorem rows_goodA_chunk1 : ∀ row ∈ (orderedRows.drop 128).take 128, GoodA row.2 := by decide +kernel
end DiophantineConsistency.ArithmeticWangTable
