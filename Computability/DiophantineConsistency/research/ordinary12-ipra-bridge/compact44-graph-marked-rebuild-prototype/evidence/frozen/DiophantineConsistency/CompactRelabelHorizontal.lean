import DiophantineConsistency.CompactRelabelBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft

theorem horizontal_permutation : horizontal.toList.Perm (List.range 250) := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.horizontal_permutation
