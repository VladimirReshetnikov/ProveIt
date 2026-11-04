import DiophantineConsistency.Compact44.CompactRelabelBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft

theorem vertical_permutation : vertical.toList.Perm (List.range 439) := by decide +kernel
end CompactRelabelDraft
#print axioms CompactRelabelDraft.vertical_permutation
