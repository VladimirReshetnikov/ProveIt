import PA194FoundationGraphRestriction
import PA194FoundationClosedSeparation
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open PA194Logic.Relational.Source (closeParameter)

def closedStrictSeparation : Proposition language :=
  closeParameter (separationFormula (strictEntryProperty (.fvar 0)))

def strictSeparationAt {Γ : List Form} (top : Nat)
    (hs : ND.Proof Γ closedStrictSeparation) :
    ND.Proof Γ (separationFormula (strictEntryProperty (.fvar top))) := by
  have hh := ND.allElim (Semiformula.rewAux Rew.fix (separationFormula (strictEntryProperty (.fvar 0)))) (.fvar top) hs
  convert hh using 1 <;> (try dsimp [closedStrictSeparation,closeParameter]) <;> (try restrictionSyntax)

#print axioms strictSeparationAt
end M6.PA.RelationalSource.PairGraph
