import DiophantineConsistency.CompactRelabelBase
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactRelabelDraft

theorem indices_sort : rowIndices.toList.mergeSort (fun x y => x ≤ y) = [0] ++ List.range' 2 941 := by decide +kernel

theorem indices_permutation_fast : rowIndices.toList.Perm ([0] ++ List.range' 2 941) := by
  have hp := (List.mergeSort_perm rowIndices.toList (fun x y => x ≤ y)).symm
  rw [indices_sort] at hp
  exact hp
end CompactRelabelDraft
#print axioms CompactRelabelDraft.indices_sort
#print axioms CompactRelabelDraft.indices_permutation_fast
