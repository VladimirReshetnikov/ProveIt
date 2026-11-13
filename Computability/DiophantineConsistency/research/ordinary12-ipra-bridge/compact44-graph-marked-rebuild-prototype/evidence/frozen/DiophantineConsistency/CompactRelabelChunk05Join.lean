import DiophantineConsistency.CompactRelabelChunk05A
import DiophantineConsistency.CompactRelabelChunk05B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_05 : (mappedOld.drop 320).take 64 = (selectedNew.drop 320).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 320 + 32 = 352 by decide, chunk_05A, chunk_05B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_05
