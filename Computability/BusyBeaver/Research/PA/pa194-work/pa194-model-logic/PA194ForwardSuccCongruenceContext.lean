import PA194ForwardSuccCongruence
import PA194ForwardReflContext
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ForwardSuccCongruence
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194SuccExtensionInputs

def contextProof : ND.Proof identityAxioms target :=
  proof ⟨⟨⟨ND.assumption (by simp [identityAxioms]),ND.assumption (by simp [identityAxioms]),
    ND.assumption (by simp [identityAxioms])⟩,ND.assumption (by simp [identityAxioms])⟩,
    ND.assumption (by simp [identityAxioms]),ND.assumption (by simp [identityAxioms]),
    ND.assumption (by simp [identityAxioms])⟩

def contextDerivation : LO.FirstOrder.Derivation
    (identityAxioms.map Semiformula.neg ++ [target]) := contextProof.contra (by simp)
#print axioms contextProof
#print axioms contextDerivation
end PA194ForwardSuccCongruence
