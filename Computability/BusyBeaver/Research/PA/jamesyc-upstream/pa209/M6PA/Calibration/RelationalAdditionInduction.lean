module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionInductionStep
@[expose] public section
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

def prefixTotal {Γ : List Form} (S : SetProofs Γ) (base : Nat)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar base)))
    (hsep : ND.Proof Γ (separationFormula (∼prefixProperty base))) :
    ND.Proof Γ (Ordinal.inductionConclusion (prefixProperty base)) :=
  Ordinal.uniformInduction S.equality.core (prefixProperty base) S.equality.transitive
    S.intersection S.adjunction hsep (prefixInductionBase S base hb) (prefixInductionStep S base)

#print axioms prefixInductionBase
#print axioms prefixInductionStep
#print axioms prefixTotal
end M6.PA.RelationalSource.PairGraph
