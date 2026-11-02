import DiophantineConsistency.CompactRelabelChunk09A
import DiophantineConsistency.CompactRelabelChunk09B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_09 : (mappedOld.drop 576).take 64 = (selectedNew.drop 576).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 576 + 32 = 608 by decide, chunk_09A, chunk_09B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_09
