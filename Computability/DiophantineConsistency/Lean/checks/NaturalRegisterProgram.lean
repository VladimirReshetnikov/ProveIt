import DiophantineConsistency.NaturalRegisterProgram

open DiophantineConsistency
open NaturalRegisterProgram

namespace NaturalRegisterProgramChecks

def p0 : Program 2 := .empty
def p1 := p0.push (.input 0)
def x1 : Fin p1.nodes.length := p0.last (.input 0)
def p2 := p1.push (.input 1)
def x2 : Fin p2.nodes.length := p1.old (.input 1) x1
def y2 : Fin p2.nodes.length := p1.last (.input 1)
def p3 := p2.push (.mul x2 x2)
def square3 : Fin p3.nodes.length := p2.last (.mul x2 x2)
def y3 : Fin p3.nodes.length := p2.old (.mul x2 x2) y2
def p4 := p3.push (.add square3 square3)
def double4 : Fin p4.nodes.length := p3.last (.add square3 square3)
def y4 : Fin p4.nodes.length := p3.old (.add square3 square3) y3

/-- The square has one register although both operands of the final sum use it. -/
example : p4.nodes.length = 4 := by decide

theorem x_realizes : p2.Realizes x2 (fun v => v 0) :=
  p1.realizes_old (.input 1) x1 (p0.realizes_input 0)

theorem square_realizes : p3.Realizes square3 (fun v => v 0 * v 0) :=
  p2.realizes_mul x2 x2 x_realizes x_realizes

theorem double_realizes : p4.Realizes double4 (fun v => (v 0 * v 0) + (v 0 * v 0)) :=
  p3.realizes_add square3 square3 square_realizes square_realizes

theorem y_realizes : p4.Realizes y4 (fun v => v 1) :=
  p3.realizes_old _ y3 (p2.realizes_old _ y2 (p1.realizes_input 1))

/-- This is a universal graph equivalence, not a finite evaluation test. -/
theorem shared_square_correct (v : Fin 2 → ℕ) :
    (v 0 * v 0) + (v 0 * v 0) = v 1 ↔
      ∃ w : Fin (p4.equalityRep double4 y4).witnessCount → ℕ,
        (p4.equalityRep double4 y4).expression.eval (natAssignment v w) = 0 := by
  simpa only [double_realizes v,y_realizes v] using
    (p4.equalityRep double4 y4).correct v

example : (p4.equalityRep double4 y4).witnessCount = 4 := by decide
example : (p4.equalityRep double4 y4).expression.binaryOps ≤ 28 :=
  p4.equalityRep_binaryOps double4 y4

#print axioms Program.cast_eval
#print axioms Program.eval_old
#print axioms Program.eval_last
#print axioms Program.realizes_add
#print axioms Program.realizes_mul
#print axioms Program.equalityRep
#print axioms Program.equalityRep_degree
#print axioms Program.equalityRep_binaryOps
#print axioms shared_square_correct

end NaturalRegisterProgramChecks
