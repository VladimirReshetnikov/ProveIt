import PA194MulRestrictionPrefix
import PA194MulPredecessorFromPrefix
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def predecessorFromRestriction {Γ : List Form} (E : FormulaEquality Γ) (t u base z g h out : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar u) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar u) (.fvar out)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h))) :
    ND.Proof Γ (predecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  have oldRec := ND.andRight (ND.andRight (ND.andRight (ND.andRight hp)))
  have prev := recurrenceAt g base u out t oldRec he hs
  have hp' := restrictionPrefix E t u base z g h ht hs hz hp hr
  have inside : ND.Proof Γ (inclusiveDomain (.fvar t) (.fvar t)) := ND.orRight (E.reflexive (.fvar t))
  have prev' := restrictPrevious t g h base t out hr inside prev
  exact fromPrefix t base z h out hz hp' prev'
#print axioms predecessorFromRestriction
end PA194MulRecurrenceNew
