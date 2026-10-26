import DiophantineConsistency.ArithmeticCertificates
import DiophantineConsistency.RegisterRelationLogic

/-! # A shared-register quotient/remainder certificate with an explicit positive guard -/

namespace DiophantineConsistency.RegisterDivMod

open NaturalRegisterProgram NaturalRegisterRelation ArithmeticDAG RegisterRelationLogic

theorem certificate_iff (q r n b : ℕ) :
    (∃ s, n = q * b + r ∧ b = r + s + 1) ↔
      0 < b ∧ q = n / b ∧ r = n % b :=
  ArithmeticCertificates.divMod_certificate_iff q r n b

/-- Source inputs are `(quotient,remainder,numerator,denominator)` and input
4 is the explicit remainder-bound slack. Shared products are computed once. -/
def program : Program 5 where
  nodes := [.input 0,.input 1,.input 2,.input 3,.input 4,.literal 1,.literal 2,
    .mul 0 3,.add 7 1,.add 1 4,.add 9 5,
    .mul 2 2,.mul 8 8,.mul 3 3,.mul 10 10,.add 11 12,.add 13 14,.add 15 16,
    .mul 2 8,.mul 3 10,.add 18 19,.mul 6 20]
  topological := by decide
  allowed := by decide

private def lhsWire : Fin program.nodes.length := ⟨17,by decide⟩
private def rhsWire : Fin program.nodes.length := ⟨21,by decide⟩

private theorem program_lhs (x : Fin 5 → ℕ) :
    program.eval x lhsWire = andLeft (x 2) (x 0 * x 3 + x 1) (x 3) (x 1 + x 4 + 1) := by
  apply Int.ofNat.inj
  change (program.eval x lhsWire : ℤ) =
    (andLeft (x 2) (x 0 * x 3 + x 1) (x 3) (x 1 + x 4 + 1) : ℤ)
  rw [Program.cast_eval]
  simp [program,lhsWire,ArithmeticDAG.value,ArithmeticDAG.run,Node.eval,andLeft]

private theorem program_rhs (x : Fin 5 → ℕ) :
    program.eval x rhsWire = andRight (x 2) (x 0 * x 3 + x 1) (x 3) (x 1 + x 4 + 1) := by
  apply Int.ofNat.inj
  change (program.eval x rhsWire : ℤ) =
    (andRight (x 2) (x 0 * x 3 + x 1) (x 3) (x 1 + x 4 + 1) : ℤ)
  rw [Program.cast_eval]
  simp [program,rhsWire,ArithmeticDAG.value,ArithmeticDAG.run,Node.eval,andRight]

/-- The guard is part of the represented predicate; zero denominators produce
no witness. No side condition is supplied to the correctness theorem. -/
def joint : Relation 4 (fun v =>
    0 < v 3 ∧ v 0 = v 2 / v 3 ∧ v 1 = v 2 % v 3) where
  auxiliaryCount := 1
  program := program
  left := lhsWire
  right := rhsWire
  correct := by
    intro v
    simp only [program_lhs,program_rhs,and_equality_iff]
    change (0 < v 3 ∧ v 0 = v 2 / v 3 ∧ v 1 = v 2 % v 3) ↔
      ∃ w : Fin 1 → ℕ, v 2 = v 0 * v 3 + v 1 ∧ v 3 = v 1 + w 0 + 1
    constructor
    · intro h
      obtain ⟨s,hs⟩ := (certificate_iff _ _ _ _).mpr h
      exact ⟨fun _ => s,hs⟩
    · rintro ⟨w,hw⟩
      exact (certificate_iff _ _ _ _).mp ⟨w 0,hw⟩

def representation : Rep (Fin 4) (fun v =>
    0 < v 3 ∧ v 0 = v 2 / v 3 ∧ v 1 = v 2 % v 3) := joint.compile

@[simp] theorem representation_witnessCount : representation.witnessCount = 23 := rfl

theorem representation_binaryOps : representation.expression.binaryOps ≤ 136 :=
  joint.compile_binaryOps

theorem representation_degree : representation.expression.toPolynomial.totalDegree ≤ 4 :=
  joint.compile_degree

end DiophantineConsistency.RegisterDivMod
