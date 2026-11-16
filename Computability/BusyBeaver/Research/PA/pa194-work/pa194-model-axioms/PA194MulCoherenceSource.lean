import PA194MulCoherenceApply
import PA194MulCoherenceSeparation
import PA194ForwardReflContext
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def axioms : List Form := negatedSeparation :: addCoherenceStatement :: closedStrictSeparation :: closedInclusiveSeparation :: identityAxioms

def contextProof : ND.Proof axioms statement := by
  let E : FormulaEquality axioms :=
    ⟨⟨ND.assumption (by simp [axioms,identityAxioms]),ND.assumption (by simp [axioms,identityAxioms]),
      ND.assumption (by simp [axioms,identityAxioms])⟩,ND.assumption (by simp [axioms,identityAxioms])⟩
  exact conclusion E (ND.assumption (by simp [axioms])) (ND.assumption (by simp [axioms,identityAxioms]))
    (ND.assumption (by simp [axioms,identityAxioms])) (ND.assumption (by simp [axioms,identityAxioms]))
    (ND.assumption (by simp [axioms])) (ND.assumption (by simp [axioms])) (ND.assumption (by simp [axioms,negatedSeparation]))

def contextDerivation : LO.FirstOrder.Derivation (axioms.map Semiformula.neg ++ [statement]) :=
  contextProof.contra (by simp [ND.Proof])
#print axioms contextProof
#print axioms contextDerivation
end PA194MulCoherence
