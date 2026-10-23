import DiophantineConsistency.RegisterCantorPairing
import DiophantineConsistency.RegisterNatPairing

open DiophantineConsistency

namespace RegisterRelationsChecks

/-- The operation used by the direct annotated checker, for every natural code. -/
theorem direct_left_correct (code out : ℕ) :
    out = (Nat.unpair code).1 ↔ ∃ w : Fin 41 → ℕ,
      RegisterNatPairing.leftGraph.expression.eval
        (natAssignment (withOutput (fun _ : Fin 1 => code) out) w) = 0 :=
  RegisterNatPairing.leftGraph.correct (withOutput (fun _ : Fin 1 => code) out)

theorem direct_right_correct (code out : ℕ) :
    out = (Nat.unpair code).2 ↔ ∃ w : Fin 41 → ℕ,
      RegisterNatPairing.rightGraph.expression.eval
        (natAssignment (withOutput (fun _ : Fin 1 => code) out) w) = 0 :=
  RegisterNatPairing.rightGraph.correct (withOutput (fun _ : Fin 1 => code) out)

example : (RegisterNatPairing.program 0 2).nodes.length = 39 := by decide
example : RegisterNatPairing.leftGraph.witnessCount = 41 := rfl
example : RegisterNatPairing.rightGraph.witnessCount = 41 := rfl
example : (RegisterCantorPairing.cantorProgram 0 2).nodes.length = 10 := by decide
example : RegisterCantorPairing.cantorLeftGraph.witnessCount = 11 := rfl

#print axioms NaturalRegisterRelation.scopedEqualityRep
#print axioms NaturalRegisterRelation.scopedEqualityRep_witnessCount
#print axioms NaturalRegisterRelation.scopedEqualityRep_degree
#print axioms NaturalRegisterRelation.scopedEqualityRep_binaryOps
#print axioms RegisterRelationLogic.and_equality_iff
#print axioms RegisterRelationLogic.or_equality_iff
#print axioms RegisterCantorPairing.cantorLeftGraph
#print axioms RegisterCantorPairing.cantorRightGraph
#print axioms RegisterCantorPairing.cantorLeftGraph_degree
#print axioms RegisterCantorPairing.cantorRightGraph_degree
#print axioms RegisterNatPairing.certificate_iff
#print axioms RegisterNatPairing.exists_certificate_iff
#print axioms RegisterNatPairing.program
#print axioms RegisterNatPairing.leftGraph_degree
#print axioms RegisterNatPairing.rightGraph_degree
#print axioms RegisterNatPairing.leftGraph_binaryOps
#print axioms RegisterNatPairing.rightGraph_binaryOps
#print axioms direct_left_correct
#print axioms direct_right_correct

end RegisterRelationsChecks
