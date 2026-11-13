import DiophantineConsistency.CompactRelabelInverseBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft
theorem forward_12 : (forwardRoundtrip.drop 768).take 64 = ((List.range 942).drop 768).take 64 := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.forward_12
