import DiophantineConsistency.CompactRelabelBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft

theorem chunk_14 : (mappedOld.drop 896).take 46 = (selectedNew.drop 896).take 46 := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.chunk_14
