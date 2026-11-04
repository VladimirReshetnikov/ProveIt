import DiophantineConsistency.Compact44.CompactRelabelChunk07A
import DiophantineConsistency.Compact44.CompactRelabelChunk07B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_07 : (mappedOld.drop 448).take 64 = (selectedNew.drop 448).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 448 + 32 = 480 by decide, chunk_07A, chunk_07B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_07
