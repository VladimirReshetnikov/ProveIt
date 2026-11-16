import PA194FoundationInverseSymmetry
import PA194TypedClosure
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194InverseClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.PairGraph
open PA194Logic.Relational.Source (closeParameter)

def inverseFullProperty : Semiproposition M6.PA.RelationalSource.language 1 :=
  ∼inverseProperty 0 1

def closedInverseSeparation : Proposition M6.PA.RelationalSource.language :=
  closeParameter (inverseClosedSeparation 0)

theorem inverseSeparation_fvSup : (separationFormula inverseFullProperty).fvSup = 2 := by decide

theorem inverseSeparation_closure :
    (separationFormula inverseFullProperty).univCl = closedInverseSeparation := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [inverseSeparation_fvSup]
  simp only [allClosure_succ,allClosure_zero,Rew.fixitr_succ,Rew.fixitr_zero,Rew.comp_id]
  simp [closedInverseSeparation,inverseFullProperty,inverseClosedSeparation,closeParameter,
    TransitiveRewriting.comp_app,app_eq_rewAux,Semiformula.rewAux]
  all_goals try finishSourceSyntax
#print axioms inverseSeparation_fvSup
#print axioms inverseSeparation_closure
end PA194InverseClosedTemplate
