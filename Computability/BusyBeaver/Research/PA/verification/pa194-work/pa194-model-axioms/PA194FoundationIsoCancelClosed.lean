import PA194FoundationIsoSuccessorCancel
import PA194FoundationStrictSeparation
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def orderIsoSuccessorCancelClosed {Γ : List Form} (E : FormulaEquality Γ) (a b p q : Nat)
    (hsep : ND.Proof Γ closedStrictSeparation)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hp : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hq : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar b)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar p) (.fvar q)) :=
  orderIsoSuccessorCancelDirect E a b p q (strictSeparationAt p hsep) hb hp hq hi

#print axioms orderIsoSuccessorCancelClosed
end M6.PA.RelationalSource.PairGraph
