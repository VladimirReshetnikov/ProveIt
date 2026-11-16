import PA194FoundationCompositionTransitivity
import PA194TypedClosure
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194CompositionClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.PairGraph
open PA194Logic.Relational.Source (closeParameter)

def compositionFullProperty : Semiproposition M6.PA.RelationalSource.language 1 :=
  ∼compositionProperty 1 0 2

def closedCompositionSeparation : Proposition M6.PA.RelationalSource.language :=
  closeParameter (compositionClosedSeparation 0)

theorem compositionSeparation_fvSup : (separationFormula compositionFullProperty).fvSup = 3 := by decide

theorem compositionSeparation_closure :
    (separationFormula compositionFullProperty).univCl = closedCompositionSeparation := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [compositionSeparation_fvSup]
  simp only [allClosure_succ,allClosure_zero,Rew.fixitr_succ,Rew.fixitr_zero,Rew.comp_id]
  simp [closedCompositionSeparation,compositionFullProperty,compositionClosedSeparation,compositionHalfSeparation,
    closeParameter,TransitiveRewriting.comp_app,app_eq_rewAux,Semiformula.rewAux]
  all_goals try finishSourceSyntax
#print axioms compositionSeparation_fvSup
#print axioms compositionSeparation_closure
end PA194CompositionClosedTemplate
