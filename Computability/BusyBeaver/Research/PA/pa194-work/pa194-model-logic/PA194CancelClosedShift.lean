import PA194StrictSeparationTemplate
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194CancelClosedShift
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.PairGraph PA194StrictSeparationTemplate

theorem closedStrictSeparation_shift : closedStrictSeparation.shift = closedStrictSeparation := by
  have hf : closedStrictSeparation.freeVariables = ∅ := by
    rw [←strictSeparation_closure, Semiformula.coe_univCl_eq_univCl']
    exact Semiformula.fvarList_univCl' _
  exact PA194ModelLogic.syntactic_noFree_shift_fixed 0 closedStrictSeparation hf
#print axioms closedStrictSeparation_shift
end PA194CancelClosedShift
