import PA194ForwardAddZeroProof
import PA194ForwardReflContext
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ForwardAddZero
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph

def contextProof : ND.Proof identityAxioms target :=
  proof ⟨⟨ND.assumption (by simp [identityAxioms]),ND.assumption (by simp [identityAxioms]),
    ND.assumption (by simp [identityAxioms])⟩,ND.assumption (by simp [identityAxioms])⟩
    (ND.assumption (by simp [identityAxioms])) (ND.assumption (by simp [identityAxioms]))
    orderIsoReflexivityDerivation

def contextDerivation : LO.FirstOrder.Derivation
    (identityAxioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp)
#print axioms contextProof
#print axioms contextDerivation
end PA194ForwardAddZero
