import PA194MulCoherenceInductionStep
import PA194MulCoherenceInductionBase
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def conclusion {Γ : List Form} (E : FormulaEquality Γ)
    (haddition : ND.Proof Γ addCoherenceStatement)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hinter : ND.Proof Γ Ordinal.intersectionFormula)
    (hstrict : ND.Proof Γ closedStrictSeparation) (hinclusive : ND.Proof Γ closedInclusiveSeparation)
    (hsep : ND.Proof Γ (separationFormula (∼property))) :
    ND.Proof Γ (Ordinal.inductionConclusion property) :=
  Ordinal.uniformInduction E.core property E.transitive hinter hadj hsep
    (inductionBase E) (inductionStep E haddition hempty hadj hstrict hinclusive)
#print axioms conclusion
end PA194MulCoherence
