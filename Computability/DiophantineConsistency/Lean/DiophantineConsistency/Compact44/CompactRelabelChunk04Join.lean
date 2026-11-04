import DiophantineConsistency.Compact44.CompactRelabelChunk04A
import DiophantineConsistency.Compact44.CompactRelabelChunk04B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_04 : (mappedOld.drop 256).take 64 = (selectedNew.drop 256).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 256 + 32 = 288 by decide, chunk_04A, chunk_04B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_04
