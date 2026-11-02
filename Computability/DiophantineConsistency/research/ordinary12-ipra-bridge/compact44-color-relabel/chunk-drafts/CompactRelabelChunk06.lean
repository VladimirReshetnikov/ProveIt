import DiophantineConsistency.CompactRelabelBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft

theorem chunk_06 : (mappedOld.drop 384).take 64 = (selectedNew.drop 384).take 64 := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_06
