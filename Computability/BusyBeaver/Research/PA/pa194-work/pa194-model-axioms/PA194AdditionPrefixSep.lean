import PA194FoundationAdditionOutputNumeric
import PA194FoundationClosedSeparation
import PA194TypedClosure
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194AdditionPrefixSep
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic.Relational.Source (closeParameter)

def property : Semiproposition M6.PA.RelationalSource.language 1 := ∼prefixProperty 0
def closedSep : Proposition M6.PA.RelationalSource.language := closeParameter (separationFormula property)

theorem fvSup_eq : (separationFormula property).fvSup = 1 := by decide

theorem closure_eq : (separationFormula property).univCl = closedSep := by
  simp only [Semiformula.coe_univCl_eq_univCl']
  unfold Semiformula.univCl'
  rw [fvSup_eq]
  simp only [allClosure_succ,allClosure_zero,Rew.fixitr_succ,Rew.fixitr_zero,Rew.comp_id]
  rfl

theorem closedSep_shift : closedSep.shift = closedSep := by
  have hf : closedSep.freeVariables = ∅ := by
    rw [←closure_eq, Semiformula.coe_univCl_eq_univCl']
    exact Semiformula.fvarList_univCl' _
  exact PA194ModelLogic.syntactic_noFree_shift_fixed 0 closedSep hf

def sepAtZero {Γ : List Form} (hs : ND.Proof Γ closedSep) :
    ND.Proof Γ (separationFormula (∼prefixProperty 0)) := by
  have hh := ND.allElim (Semiformula.rewAux Rew.fix (separationFormula property)) (.fvar 0) hs
  convert hh using 1 <;> (try dsimp [closedSep,closeParameter,property]) <;> (try prefixSyntax)
#print axioms closure_eq
#print axioms closedSep_shift
#print axioms sepAtZero
end PA194AdditionPrefixSep
