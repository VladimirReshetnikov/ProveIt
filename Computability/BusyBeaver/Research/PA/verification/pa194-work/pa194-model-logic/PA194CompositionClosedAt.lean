import PA194CompositionClosedTemplate
import PA194FoundationInverseSpecialize
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194CompositionClosedTemplate
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194Logic.Relational.Source (closeParameter)
variable {Γ : List Form}

def compositionClosedAt (a : Nat) (h : ND.Proof Γ closedCompositionSeparation) :
    ND.Proof Γ (compositionClosedSeparation a) := by
  have hh := specializeParameter (compositionClosedSeparation 0) (.fvar a) h
  convert hh using 1 <;> (dsimp [compositionClosedSeparation,compositionHalfSeparation,closeParameter,compositionProperty,separationFormula] <;> compositionSyntax)
#print axioms compositionClosedAt
end PA194CompositionClosedTemplate
