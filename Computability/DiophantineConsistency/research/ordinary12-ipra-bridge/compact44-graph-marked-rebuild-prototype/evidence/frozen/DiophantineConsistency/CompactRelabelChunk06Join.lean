import DiophantineConsistency.CompactRelabelChunk06A
import DiophantineConsistency.CompactRelabelChunk06B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_06 : (mappedOld.drop 384).take 64 = (selectedNew.drop 384).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 384 + 32 = 416 by decide, chunk_06A, chunk_06B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_06
