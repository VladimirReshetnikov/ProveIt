import DiophantineConsistency.Compact44.CompactRelabelChunk12A
import DiophantineConsistency.Compact44.CompactRelabelChunk12B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_12 : (mappedOld.drop 768).take 64 = (selectedNew.drop 768).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 768 + 32 = 800 by decide, chunk_12A, chunk_12B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_12
