import PA194ForwardSuccInjectiveProof
import PA194IsoCancelStatement
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ForwardSuccInjective
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194CancelInputs

def contextProof : ND.Proof isoCancelAxioms target :=
  proof ⟨⟨⟨ND.assumption (by simp [isoCancelAxioms,greatestImageAxioms]),
    ND.assumption (by simp [isoCancelAxioms,greatestImageAxioms]),
    ND.assumption (by simp [isoCancelAxioms,greatestImageAxioms])⟩,
    ND.assumption (by simp [isoCancelAxioms,greatestImageAxioms])⟩,
    ND.assumption (by simp [isoCancelAxioms])⟩

def contextDerivation : LO.FirstOrder.Derivation
    (isoCancelAxioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp)
#print axioms contextProof
#print axioms contextDerivation
end PA194ForwardSuccInjective
