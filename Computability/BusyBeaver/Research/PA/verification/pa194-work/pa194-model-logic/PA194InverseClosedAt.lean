import PA194InverseClosedTemplate
import PA194FoundationInverseSpecialize
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194InverseClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic.Relational.Source (closeParameter)
variable {Γ : List Form}

def inverseClosedAt (a : Nat) (h : ND.Proof Γ closedInverseSeparation) :
    ND.Proof Γ (inverseClosedSeparation a) := by
  have hh := specializeParameter (inverseClosedSeparation 0) (.fvar a) h
  convert hh using 1 <;> (dsimp [inverseClosedSeparation,closeParameter,inverseProperty,separationFormula] <;> inverseSyntax)
#print axioms inverseClosedAt
end PA194InverseClosedTemplate
