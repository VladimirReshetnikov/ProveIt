import PA194InclusiveSeparation
import PA194TypedClosure
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194InclusiveSeparationClosure
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic.Relational.Source (closeParameter)

def property : Semiproposition M6.PA.RelationalSource.language 1 := domainEntryProperty (.fvar 0)

theorem fvSup_eq : (separationFormula property).fvSup = 1 := by decide

theorem closure_eq : (separationFormula property).univCl = closedInclusiveSeparation := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [fvSup_eq]
  simp only [allClosure_succ,allClosure_zero,Rew.fixitr_succ,Rew.fixitr_zero,Rew.comp_id]
  rfl

theorem closedSep_shift : closedInclusiveSeparation.shift = closedInclusiveSeparation := by
  have hf : closedInclusiveSeparation.freeVariables = ∅ := by
    rw [←closure_eq, Semiformula.coe_univCl_eq_univCl']
    exact Semiformula.fvarList_univCl' _
  exact PA194ModelLogic.syntactic_noFree_shift_fixed 0 closedInclusiveSeparation hf

#print axioms fvSup_eq
#print axioms closure_eq
#print axioms closedSep_shift
end PA194InclusiveSeparationClosure
