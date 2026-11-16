import PA194MulResultPredecessor
import PA194InclusiveSeparation
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def resultPredecessorClosed {Γ : List Form} (E : FormulaEquality Γ) (t u base out : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hp : ND.Proof Γ (mulResult (.fvar u) (.fvar base) (.fvar out)))
    (hsep : ND.Proof Γ closedInclusiveSeparation) :
    ND.Proof Γ (predecessorResult (.fvar t) (.fvar base) (.fvar out)) :=
  resultPredecessor E t u base out ht hs hp (inclusiveSeparationAt t hsep)
#print axioms resultPredecessorClosed
end PA194MulRecurrenceNew
