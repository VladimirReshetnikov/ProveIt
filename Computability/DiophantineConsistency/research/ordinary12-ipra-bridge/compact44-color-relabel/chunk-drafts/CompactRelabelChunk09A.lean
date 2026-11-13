import DiophantineConsistency.CompactRelabelBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft

theorem chunk_09A : (mappedOld.drop 576).take 32 = (selectedNew.drop 576).take 32 := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_09A
