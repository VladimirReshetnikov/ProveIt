import DiophantineConsistency.Compact44.CompactRelabelAssembly
import DiophantineConsistency.Compact44.CompactRelabelHorizontal
import DiophantineConsistency.Compact44.CompactRelabelVertical
import DiophantineConsistency.Compact44.CompactRelabelInverseAssembly
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactRelabelDraft

theorem finite_table_correspondence :
    mappedOld = selectedNew ∧
    horizontal.toList.Perm (List.range 250) ∧
    vertical.toList.Perm (List.range 439) ∧
    rowIndices.toList.Perm compactIndices :=
  ⟨full_row_equality, horizontal_permutation, vertical_permutation, indices_permutation⟩
end CompactRelabelDraft
#print axioms CompactRelabelDraft.finite_table_correspondence
