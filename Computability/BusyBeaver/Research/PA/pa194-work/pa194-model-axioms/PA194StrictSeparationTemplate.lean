import PA194FoundationStrictSeparation
import PA194TypedClosure
set_option maxHeartbeats 5000000
namespace PA194StrictSeparationTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.PairGraph
open PA194Logic.Relational.Source (closeParameter)

def strictProperty : Semiproposition M6.PA.RelationalSource.language 1 :=
  strictEntryProperty (.fvar 0)

theorem strictSeparation_fvSup : (separationFormula strictProperty).fvSup = 1 := by decide

theorem strictSeparation_closure : (separationFormula strictProperty).univCl = closedStrictSeparation := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [strictSeparation_fvSup]
  simp only [allClosure_succ,allClosure_zero,Rew.fixitr_succ,Rew.fixitr_zero,Rew.comp_id]
  rfl

#print axioms strictSeparation_fvSup
#print axioms strictSeparation_closure
end PA194StrictSeparationTemplate
