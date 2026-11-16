import PA194CompositionClosedTemplate
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194CompositionClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource

theorem closedCompositionSeparation_shift_fast : closedCompositionSeparation.shift = closedCompositionSeparation := by
  have hf : closedCompositionSeparation.freeVariables = ∅ := by
    rw [←compositionSeparation_closure, Semiformula.coe_univCl_eq_univCl']
    exact Semiformula.fvarList_univCl' _
  exact PA194ModelLogic.syntactic_noFree_shift_fixed 0 closedCompositionSeparation hf
#print axioms closedCompositionSeparation_shift_fast
end PA194CompositionClosedTemplate
