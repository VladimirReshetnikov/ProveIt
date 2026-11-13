import DiophantineConsistency.CompactRelabelBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft

theorem indices_permutation : rowIndices.toList.Perm ([0] ++ List.range' 2 941) := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.indices_permutation
