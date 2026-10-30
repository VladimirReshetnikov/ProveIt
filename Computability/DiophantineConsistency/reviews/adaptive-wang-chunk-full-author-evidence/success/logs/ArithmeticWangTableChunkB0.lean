import DiophantineConsistency.ArithmeticWangTableChunkCore
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace DiophantineConsistency.ArithmeticWangTable
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open WangTiles942
/-- One finite chunk of the original GoodB predicate. -/
theorem rows_goodB_chunk0 : ∀ row ∈ orderedRows.take 128, GoodB row.2 := by decide +kernel
end DiophantineConsistency.ArithmeticWangTable
