import DiophantineConsistency.Compact44.CompactRelabelInverseBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft
theorem forward_14 : (forwardRoundtrip.drop 896).take 46 = ((List.range 942).drop 896).take 46 := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.forward_14
