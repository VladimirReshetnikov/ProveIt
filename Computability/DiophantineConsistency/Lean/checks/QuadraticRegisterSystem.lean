import DiophantineConsistency.QuadraticNatPairing
import DiophantineConsistency.QuadraticDivMod
import DiophantineConsistency.RegisterDivMod

open DiophantineConsistency

namespace QuadraticRegisterSystemChecks

theorem direct_left_correct (code out : ℕ) :
    out = (Nat.unpair code).1 ↔ ∃ w : Fin 4 → ℕ,
      QuadraticNatPairing.leftGraph.expression.eval
        (natAssignment (withOutput (fun _ : Fin 1 => code) out) w) = 0 :=
  QuadraticNatPairing.leftGraph.correct (withOutput (fun _ : Fin 1 => code) out)

theorem direct_right_correct (code out : ℕ) :
    out = (Nat.unpair code).2 ↔ ∃ w : Fin 4 → ℕ,
      QuadraticNatPairing.rightGraph.expression.eval
        (natAssignment (withOutput (fun _ : Fin 1 => code) out) w) = 0 :=
  QuadraticNatPairing.rightGraph.correct (withOutput (fun _ : Fin 1 => code) out)

theorem pair_correct (z a b : ℕ) : z = Nat.pair a b ↔ ∃ w : Fin 3 → ℕ,
    QuadraticNatPairing.pairRepresentation.expression.eval (natAssignment ![a,z,b] w) = 0 :=
  QuadraticNatPairing.pairRepresentation.correct ![a,z,b]

theorem guarded_joint_correct (q r n b : ℕ) :
    (0 < b ∧ q = n / b ∧ r = n % b) ↔ ∃ w : Fin 1 → ℕ,
      QuadraticDivMod.representation.expression.eval (natAssignment ![q,r,n,b] w) = 0 :=
  QuadraticDivMod.representation.correct ![q,r,n,b]

theorem zero_denominator_has_no_witness (q r n : ℕ) : ¬ ∃ w : Fin 1 → ℕ,
    QuadraticDivMod.representation.expression.eval (natAssignment ![q,r,n,0] w) = 0 := by
  intro h
  exact (Nat.lt_irrefl 0) ((guarded_joint_correct q r n 0).mpr h).1

example : RegisterDivMod.representation.witnessCount = 23 := rfl
example : QuadraticDivMod.representation.witnessCount = 1 := rfl

#print axioms QuadraticRegisterSystem.polynomial_degree_le
#print axioms QuadraticRegisterSystem.System.expression_zero_iff
#print axioms QuadraticRegisterSystem.System.representation
#print axioms QuadraticRegisterSystem.System.scopedRep
#print axioms QuadraticRegisterSystem.System.scopedRep_degree
#print axioms QuadraticNatPairing.certificate_sound
#print axioms QuadraticNatPairing.certificate_complete
#print axioms QuadraticNatPairing.pairRepresentation_degree
#print axioms QuadraticNatPairing.leftGraph_degree
#print axioms QuadraticNatPairing.rightGraph_degree
#print axioms QuadraticNatPairing.leftGraph_binaryOps
#print axioms QuadraticDivMod.representation
#print axioms QuadraticDivMod.representation_degree
#print axioms QuadraticDivMod.representation_binaryOps
#print axioms RegisterDivMod.representation
#print axioms direct_left_correct
#print axioms direct_right_correct
#print axioms pair_correct
#print axioms guarded_joint_correct
#print axioms zero_denominator_has_no_witness

end QuadraticRegisterSystemChecks
