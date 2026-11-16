import PA194ForwardTransitivityProof
import PA194CompositionContext
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ForwardTransitivity
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194CompositionInputs PA194CompositionContext PA194CompositionClosedTemplate

def contextProof : ND.Proof compositionAxioms target :=
  proof ⟨⟨⟨ND.assumption (by simp [compositionAxioms]),ND.assumption (by simp [compositionAxioms]),
    ND.assumption (by simp [compositionAxioms])⟩,ND.assumption (by simp [compositionAxioms])⟩,
    ND.assumption (by simp [compositionAxioms]),ND.assumption (by simp [compositionAxioms]),
    ND.assumption (by simp [compositionAxioms]),ND.assumption (by simp [compositionAxioms])⟩

def contextDerivation : LO.FirstOrder.Derivation
    (compositionAxioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp)
#print axioms contextProof
#print axioms contextDerivation
end PA194ForwardTransitivity
