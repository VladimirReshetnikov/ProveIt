import DiophantineConsistency.Compact44.CompactRelabelChunk08A
import DiophantineConsistency.Compact44.CompactRelabelChunk08B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_08 : (mappedOld.drop 512).take 64 = (selectedNew.drop 512).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 512 + 32 = 544 by decide, chunk_08A, chunk_08B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_08
