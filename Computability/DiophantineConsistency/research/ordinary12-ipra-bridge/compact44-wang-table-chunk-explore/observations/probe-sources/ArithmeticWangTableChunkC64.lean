import DiophantineConsistency.ArithmeticWangTableChunkCover
import DiophantineConsistency.ArithmeticWangTableChunkC00
import DiophantineConsistency.ArithmeticWangTableChunkC01
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticWangTable
open DiophantineConsistency.WangTiles942
theorem rows_goodC_first64 : ∀ row ∈ orderedRows.take 64, GoodC row.2 := by
  apply chunk_cover (fun row => GoodC row.2) (orderedRows.take 64) 32
  · simpa only [List.take_take, Nat.min_eq_left (by decide : 32≤64)] using rows_goodC_chunk00
  · exact rows_goodC_chunk01
#print axioms DiophantineConsistency.ArithmeticWangTable.rows_goodC_first64
end DiophantineConsistency.ArithmeticWangTable
