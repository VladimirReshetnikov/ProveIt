import DiophantineConsistency.Compact44.CompactRelabelChunk11A
import DiophantineConsistency.Compact44.CompactRelabelChunk11B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_11 : (mappedOld.drop 704).take 64 = (selectedNew.drop 704).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 704 + 32 = 736 by decide, chunk_11A, chunk_11B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_11
