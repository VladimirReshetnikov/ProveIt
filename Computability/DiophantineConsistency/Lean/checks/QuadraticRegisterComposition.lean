import DiophantineConsistency.QuadraticTreeCodeGraphs
import DiophantineConsistency.AnnotatedCodeGraphs

open DiophantineConsistency
open NaturalRegisterProgram QuadraticRegisterSystem

namespace QuadraticRegisterCompositionChecks

/-- A genuine nonempty register bank: both input values and one shared square. -/
def squareProgram : Program 2 where
  nodes := [.input 0,.input 1,.mul 0 0]
  topological := by decide
  allowed := by decide

private def squareWire : Fin squareProgram.nodes.length := ⟨2,by decide⟩
private def ports : Fin 2 → Slot squareProgram := ![.inl 1,.inr squareWire]

def attached : System squareProgram :=
  QuadraticTreeCodeGraphs.predSystem.instantiate squareProgram ports

private theorem square_value (x : Fin 2 → ℕ) : squareProgram.eval x squareWire = x 0 * x 0 := by
  apply Int.ofNat.inj
  change (squareProgram.eval x squareWire : ℤ) = ((x 0 * x 0 : ℕ) : ℤ)
  rw [Program.cast_eval]
  simp [squareProgram,squareWire,ArithmeticDAG.value,ArithmeticDAG.run,ArithmeticDAG.Node.eval]

/-- The attached relation reads a stored square; it does not inline its producer. -/
theorem attachment_correct (x : Fin 2 → ℕ) : attached.Holds x ↔ x 1 = (x 0 * x 0).pred := by
  calc
    attached.Holds x ↔ QuadraticTreeCodeGraphs.predSystem.Holds
        (fun i => slotValue squareProgram x (ports i)) :=
      System.instantiate_holds QuadraticTreeCodeGraphs.predSystem squareProgram ports x
    _ ↔ slotValue squareProgram x (ports 0) = (slotValue squareProgram x (ports 1)).pred :=
      QuadraticTreeCodeGraphs.pred_holds_iff _
    _ ↔ x 1 = (x 0 * x 0).pred := by
      change (x 1 = (squareProgram.eval x squareWire).pred) ↔ _
      rw [square_value]

example : attached.representation.witnessCount = 3 := rfl

theorem treeLeft_correct (code out : ℕ) :
    out = AnnotatedCodeArithmetic.treeLeft code ↔ ∃ w : Fin 5 → ℕ,
      QuadraticTreeCodeGraphs.treeLeft.expression.eval
        (natAssignment (withOutput (fun _ : Fin 1 => code) out) w) = 0 :=
  QuadraticTreeCodeGraphs.treeLeft.correct (withOutput (fun _ : Fin 1 => code) out)

theorem treeRight_correct (code out : ℕ) :
    out = AnnotatedCodeArithmetic.treeRight code ↔ ∃ w : Fin 5 → ℕ,
      QuadraticTreeCodeGraphs.treeRight.expression.eval
        (natAssignment (withOutput (fun _ : Fin 1 => code) out) w) = 0 :=
  QuadraticTreeCodeGraphs.treeRight.correct (withOutput (fun _ : Fin 1 => code) out)

theorem listTail_correct (code out : ℕ) :
    out = AnnotatedCodeArithmetic.listTail code ↔ ∃ w : Fin 5 → ℕ,
      QuadraticTreeCodeGraphs.listTail.expression.eval
        (natAssignment (withOutput (fun _ : Fin 1 => code) out) w) = 0 :=
  QuadraticTreeCodeGraphs.listTail.correct (withOutput (fun _ : Fin 1 => code) out)

theorem nil_output_iff (out : ℕ) : out = 0 ↔ ∃ w : Fin 5 → ℕ,
    QuadraticTreeCodeGraphs.listTail.expression.eval
      (natAssignment (withOutput (fun _ : Fin 1 => 0) out) w) = 0 :=
  listTail_correct 0 out

theorem baseline_treeLeft_ops : AnnotatedCodeGraphs.treeLeft.expression.binaryOps = 115 := by decide

theorem baseline_treeRight_ops : AnnotatedCodeGraphs.treeRight.expression.binaryOps = 115 := by decide

theorem baseline_listTail_ops : AnnotatedCodeGraphs.listTail.expression.binaryOps = 3879 := by decide

theorem baseline_treeLeft_degree_bound : AnnotatedCodeGraphs.treeLeft.expression.toPolynomial.totalDegree ≤ 16 :=
  (QuadraticRegisterSystem.polynomial_degree_le AnnotatedCodeGraphs.treeLeft.expression).trans (by decide)

theorem baseline_treeRight_degree_bound : AnnotatedCodeGraphs.treeRight.expression.toPolynomial.totalDegree ≤ 16 :=
  (QuadraticRegisterSystem.polynomial_degree_le AnnotatedCodeGraphs.treeRight.expression).trans (by decide)

theorem baseline_listTail_degree_bound : AnnotatedCodeGraphs.listTail.expression.toPolynomial.totalDegree ≤ 512 :=
  (QuadraticRegisterSystem.polynomial_degree_le AnnotatedCodeGraphs.listTail.expression).trans (by decide)

example : AnnotatedCodeGraphs.listTail.witnessCount = 9 := AnnotatedCodeGraphs.listTail_witnessCount
example : QuadraticTreeCodeGraphs.listTail.witnessCount = 5 := rfl

#print axioms System.conjunction
#print axioms System.conjunction_holds
#print axioms System.instantiate
#print axioms System.instantiate_holds
#print axioms System.conjunction_witnessCount
#print axioms QuadraticTreeCodeGraphs.pred_certificate_iff
#print axioms QuadraticTreeCodeGraphs.left_holds_iff
#print axioms QuadraticTreeCodeGraphs.right_holds_iff
#print axioms QuadraticTreeCodeGraphs.treeLeft_degree
#print axioms QuadraticTreeCodeGraphs.treeRight_degree
#print axioms QuadraticTreeCodeGraphs.listTail_degree
#print axioms QuadraticTreeCodeGraphs.treeLeft_binaryOps
#print axioms QuadraticTreeCodeGraphs.listTail_eq_treeRight
#print axioms attachment_correct
#print axioms treeLeft_correct
#print axioms treeRight_correct
#print axioms listTail_correct
#print axioms nil_output_iff
#print axioms baseline_treeLeft_ops
#print axioms baseline_treeRight_ops
#print axioms baseline_listTail_ops
#print axioms baseline_treeLeft_degree_bound
#print axioms baseline_treeRight_degree_bound
#print axioms baseline_listTail_degree_bound

end QuadraticRegisterCompositionChecks
