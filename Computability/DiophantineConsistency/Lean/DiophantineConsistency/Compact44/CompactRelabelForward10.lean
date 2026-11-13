import DiophantineConsistency.Compact44.CompactRelabelInverseBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft
theorem forward_10 : (forwardRoundtrip.drop 640).take 64 = ((List.range 942).drop 640).take 64 := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.forward_10
