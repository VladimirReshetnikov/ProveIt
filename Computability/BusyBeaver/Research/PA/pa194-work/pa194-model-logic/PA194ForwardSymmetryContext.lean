import PA194ForwardSymmetryProof
import PA194InverseSymmetryContext
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ForwardSymmetry
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph
open PA194InverseSymmetryInputs PA194InverseSymmetryContext PA194InverseClosedTemplate

def contextProof : ND.Proof inverseSymmetryAxioms target :=
  proof ⟨⟨⟨ND.assumption (by simp [inverseSymmetryAxioms]),ND.assumption (by simp [inverseSymmetryAxioms]),
    ND.assumption (by simp [inverseSymmetryAxioms])⟩,ND.assumption (by simp [inverseSymmetryAxioms])⟩,
    ND.assumption (by simp [inverseSymmetryAxioms]),ND.assumption (by simp [inverseSymmetryAxioms]),
    ND.assumption (by simp [inverseSymmetryAxioms]),ND.assumption (by simp [inverseSymmetryAxioms])⟩

def contextDerivation : LO.FirstOrder.Derivation
    (inverseSymmetryAxioms.map Semiformula.neg ++ [target]) :=
  contextProof.contra (by simp)
#print axioms contextProof
#print axioms contextDerivation
end PA194ForwardSymmetry
