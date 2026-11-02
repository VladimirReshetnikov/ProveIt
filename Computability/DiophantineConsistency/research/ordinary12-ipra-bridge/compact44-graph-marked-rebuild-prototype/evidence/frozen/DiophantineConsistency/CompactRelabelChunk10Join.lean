import DiophantineConsistency.CompactRelabelChunk10A
import DiophantineConsistency.CompactRelabelChunk10B
set_option autoImplicit false
set_option Elab.async false
namespace CompactRelabelDraft

theorem chunk_10 : (mappedOld.drop 640).take 64 = (selectedNew.drop 640).take 64 := by
  rw [show 64 = 32 + 32 by decide, List.take_add, List.take_add]
  simp only [List.drop_drop, show 640 + 32 = 672 by decide, chunk_10A, chunk_10B]
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_10
