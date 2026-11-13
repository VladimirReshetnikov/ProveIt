import DiophantineConsistency.CompactRelabelChunk13A
import DiophantineConsistency.CompactRelabelChunk13B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_13 : (mappedOld.drop 832).take 64 = (selectedNew.drop 832).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 832 + 32 = 864 by decide, chunk_13A, chunk_13B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_13
