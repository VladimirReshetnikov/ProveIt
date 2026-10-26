import DiophantineConsistency.ArithmeticCertificates
import DiophantineConsistency.QuadraticRegisterSystem
import DiophantineConsistency.RegisterRelationLogic

/-! # A shared-register quotient/remainder certificate with an explicit positive guard -/

namespace DiophantineConsistency.QuadraticDivMod

open NaturalRegisterProgram NaturalRegisterRelation ArithmeticDAG RegisterRelationLogic QuadraticRegisterSystem

theorem certificate_iff (q r n b : ℕ) :
    (∃ s, n = q * b + r ∧ b = r + s + 1) ↔
      0 < b ∧ q = n / b ∧ r = n % b :=
  ArithmeticCertificates.divMod_certificate_iff q r n b

/-- Source inputs are `(quotient,remainder,numerator,denominator)` and input
4 is the explicit remainder-bound slack. The local constraints need no gates. -/
def program : Program 5 := .empty

private def input (i : Fin 5) : Expr (Fin 5 ⊕ Fin program.nodes.length) := .var (.inl i)

def rows : Fin 2 → Expr (Fin 5 ⊕ Fin program.nodes.length) :=
  ![input 2 - (input 0 * input 3 + input 1),
    input 3 - (input 1 + input 4 + 1)]

def system : System program := System.ofRows 2 rows (by
  intro i
  fin_cases i <;> decide)

theorem holds_iff (x : Fin 5 → ℕ) :
    system.Holds x ↔ x 2 = x 0 * x 3 + x 1 ∧ x 3 = x 1 + x 4 + 1 := by
  simp only [System.Holds,system,System.ofRows,Fin.forall_fin_two]
  change (((x 2 : ℤ) - ((x 0 : ℤ) * (x 3 : ℤ) + (x 1 : ℤ)) = 0) ∧
    ((x 3 : ℤ) - ((x 1 : ℤ) + (x 4 : ℤ) + 1) = 0)) ↔ _
  simp only [sub_eq_zero,←Int.natCast_mul,←Int.natCast_add,Int.natCast_inj]
  omega

/-- The guard is part of the represented predicate; zero denominators produce
no witness. No side condition is supplied to the correctness theorem. -/
def representation : Rep (Fin 4) (fun v =>
    0 < v 3 ∧ v 0 = v 2 / v 3 ∧ v 1 = v 2 % v 3) :=
  (System.scopedRep (a := 4) (k := 1) system).ofIff (by
    intro v
    simp only [holds_iff]
    change (∃ w : Fin 1 → ℕ, v 2 = v 0 * v 3 + v 1 ∧ v 3 = v 1 + w 0 + 1) ↔ _
    constructor
    · rintro ⟨w,hw⟩
      exact (certificate_iff _ _ _ _).mp ⟨w 0,hw⟩
    · intro h
      obtain ⟨s,hs⟩ := (certificate_iff _ _ _ _).mpr h
      exact ⟨fun _ => s,hs⟩)

@[simp] theorem representation_witnessCount : representation.witnessCount = 1 := rfl

theorem representation_binaryOps : representation.expression.binaryOps = 16 := by decide

theorem representation_degree : representation.expression.toPolynomial.totalDegree ≤ 4 :=
  System.scopedRep_degree (a := 4) (k := 1) system

end DiophantineConsistency.QuadraticDivMod
