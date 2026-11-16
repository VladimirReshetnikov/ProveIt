import PA194MulInductionStep
import PA194MulAdditionSupply
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def prefixTotal {Γ : List Form} (E : FormulaEquality Γ) (base : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hinter : ND.Proof Γ Ordinal.intersectionFormula)
    (ha1 : ND.Proof Γ PA194AdditionTotalGuardedSource.target)
    (hbase : ND.Proof Γ (Ordinal.domain (.fvar base)))
    (hsep : ND.Proof Γ (separationFormula (∼property base))) :
    ND.Proof Γ (Ordinal.inductionConclusion (property base)) :=
  Ordinal.uniformInduction E.core (property base) E.transitive hinter hadj hsep
    (inductionBase E base hempty hadj)
    (inductionStep E base hempty hadj (supplyFromA1 base ha1 hbase))
#print axioms prefixTotal
end PA194MulRecurrenceNew
