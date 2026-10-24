import DiophantineConsistency.QuadraticListHead
import DiophantineConsistency.AnnotatedCodeGraphs

open DiophantineConsistency

namespace QuadraticListHeadChecks

theorem correct (code out : ℕ) : out = AnnotatedCodeArithmetic.listHead code ↔
    ∃ w : Fin 7 → ℕ, QuadraticListHead.listHead.expression.eval
      (natAssignment (withOutput (fun _ : Fin 1 => code) out) w) = 0 :=
  QuadraticListHead.listHead.correct (withOutput (fun _ : Fin 1 => code) out)

theorem nil_correct (out : ℕ) : out = 0 ↔
    ∃ w : Fin 7 → ℕ, QuadraticListHead.listHead.expression.eval
      (natAssignment (withOutput (fun _ : Fin 1 => 0) out) w) = 0 := by
  simpa using correct 0 out

theorem cons_correct (x out : ℕ) (xs : List ℕ) : out = x + 1 ↔
    ∃ w : Fin 7 → ℕ, QuadraticListHead.listHead.expression.eval
      (natAssignment (withOutput (fun _ : Fin 1 => AnnotatedCodeArithmetic.listCode (x::xs)) out) w) = 0 := by
  simpa using correct (AnnotatedCodeArithmetic.listCode (x::xs)) out

/-- A found zero is represented by one, while nil is represented by zero. -/
theorem found_zero_correct (out : ℕ) (xs : List ℕ) : out = 1 ↔
    ∃ w : Fin 7 → ℕ, QuadraticListHead.listHead.expression.eval
      (natAssignment (withOutput (fun _ : Fin 1 => AnnotatedCodeArithmetic.listCode (0::xs)) out) w) = 0 := by
  simpa using cons_correct 0 out xs

theorem baseline_ops : AnnotatedCodeGraphs.listHead.expression.binaryOps = 8231 := by decide

theorem baseline_degree_bound : AnnotatedCodeGraphs.listHead.expression.toPolynomial.totalDegree ≤ 1024 :=
  (QuadraticRegisterSystem.polynomial_degree_le AnnotatedCodeGraphs.listHead.expression).trans (by decide)

example : AnnotatedCodeGraphs.listHead.witnessCount = 11 := AnnotatedCodeGraphs.listHead_witnessCount
example : QuadraticListHead.listHead.witnessCount = 7 := rfl
example : QuadraticListHead.listHead.expression.binaryOps = 76 := QuadraticListHead.listHead_binaryOps

#print axioms QuadraticListHead.listHead_le
#print axioms QuadraticListHead.guard_sound
#print axioms QuadraticListHead.guard_complete
#print axioms QuadraticListHead.guard_holds_iff
#print axioms QuadraticListHead.holds_iff
#print axioms QuadraticListHead.listHead_degree
#print axioms QuadraticListHead.listHead_binaryOps
#print axioms correct
#print axioms nil_correct
#print axioms cons_correct
#print axioms found_zero_correct
#print axioms baseline_ops
#print axioms baseline_degree_bound

end QuadraticListHeadChecks
