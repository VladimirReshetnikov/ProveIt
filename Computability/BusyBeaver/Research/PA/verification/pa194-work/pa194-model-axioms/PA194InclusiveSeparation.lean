import PA194InclusiveGraphRestriction
import PA194FoundationInverseSpecialize
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open PA194Logic.Relational.Source

def closedInclusiveSeparation : Proposition language :=
  closeParameter (separationFormula (domainEntryProperty (.fvar 0)))

def inclusiveSeparationAt {Γ : List ND.Form} (top : Nat)
    (hs : ND.Proof Γ closedInclusiveSeparation) :
    ND.Proof Γ (separationFormula (domainEntryProperty (.fvar top))) := by
  have hh := specializeParameter (separationFormula (domainEntryProperty (.fvar 0)))
    (.fvar top) hs
  convert hh using 1 <;> inclusiveRestrictionSyntax

def inclusiveCutFromClosedSeparation {Γ : List ND.Form} (top g : Nat)
    (hs : ND.Proof Γ closedInclusiveSeparation) :
    ND.Proof Γ (inclusiveGraphCutExists (.fvar top) (.fvar g)) :=
  inclusiveCutExists top g (inclusiveSeparationAt top hs)

#print axioms inclusiveSeparationAt
#print axioms inclusiveCutFromClosedSeparation
end M6.PA.RelationalSource.PairGraph
