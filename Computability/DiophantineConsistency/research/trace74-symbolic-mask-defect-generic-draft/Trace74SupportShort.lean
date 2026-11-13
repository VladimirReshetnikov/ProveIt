import DiophantineConsistency.CompactConcreteMask
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74SupportShort
open Finset CompactConcreteMask

/-- Only the small selector support is exposed in this isolated check. -/
theorem support_short : support ⊆ Finset.range 3297 := by
  intro j hj
  simp only [support, Finset.mem_sdiff, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton] at hj ⊢
  omega

#print axioms Trace74SupportShort.support_short
end Trace74SupportShort
