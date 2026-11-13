import DiophantineConsistency.Compact44.CompactRelabelBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft

theorem chunk_10B : (mappedOld.drop 672).take 32 = (selectedNew.drop 672).take 32 := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_10B
