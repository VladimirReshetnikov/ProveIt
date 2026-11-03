import DiophantineConsistency.Ordinary12FreeJ

/-! A finite 95-row program independently transcribed from pinned retained
JSON. File-to-table correspondence is an external provenance boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 1200000
noncomputable section
namespace FreeJRetainedProgram
open DiophantineConsistency
open AdaptiveEquationSyntax2011 Ordinary12FreeJ

inductive Ref where
  | var : Fin 12 → Ref
  | port : Fin 4 → Ref
  | lit : ℤ → Ref
  | gate : Nat → Ref

inductive Op where | add | sub | mul
structure Row where
  op : Op
  left : Ref
  right : Ref

def program : List Row := [
    ⟨.mul, .var 0, .port 0⟩,
    ⟨.add, .lit 1, .gate 0⟩,
    ⟨.mul, .gate 1, .gate 1⟩,
    ⟨.mul, .gate 1, .gate 2⟩,
    ⟨.mul, .var 6, .gate 2⟩,
    ⟨.sub, .gate 1, .var 1⟩,
    ⟨.sub, .gate 5, .var 2⟩,
    ⟨.mul, .var 5, .var 6⟩,
    ⟨.add, .var 8, .var 9⟩,
    ⟨.mul, .var 6, .gate 8⟩,
    ⟨.add, .var 8, .gate 9⟩,
    ⟨.mul, .gate 10, .gate 10⟩,
    ⟨.add, .gate 7, .var 6⟩,
    ⟨.mul, .lit 4, .gate 12⟩,
    ⟨.add, .lit 3, .gate 13⟩,
    ⟨.mul, .gate 12, .gate 12⟩,
    ⟨.add, .gate 14, .gate 15⟩,
    ⟨.mul, .gate 12, .gate 10⟩,
    ⟨.add, .var 5, .gate 17⟩,
    ⟨.mul, .gate 7, .gate 9⟩,
    ⟨.mul, .gate 3, .gate 0⟩,
    ⟨.mul, .port 1, .gate 1⟩,
    ⟨.add, .var 5, .gate 21⟩,
    ⟨.mul, .gate 6, .gate 22⟩,
    ⟨.mul, .var 1, .gate 1⟩,
    ⟨.sub, .gate 23, .gate 24⟩,
    ⟨.add, .gate 19, .gate 8⟩,
    ⟨.add, .gate 26, .var 7⟩,
    ⟨.mul, .gate 8, .gate 25⟩,
    ⟨.sub, .gate 27, .gate 28⟩,
    ⟨.mul, .gate 20, .gate 29⟩,
    ⟨.mul, .var 6, .gate 0⟩,
    ⟨.add, .gate 30, .gate 31⟩,
    ⟨.mul, .gate 3, .gate 25⟩,
    ⟨.sub, .gate 32, .gate 33⟩,
    ⟨.mul, .gate 34, .gate 34⟩,
    ⟨.mul, .gate 20, .gate 20⟩,
    ⟨.mul, .gate 19, .gate 26⟩,
    ⟨.add, .lit 1, .gate 37⟩,
    ⟨.mul, .gate 36, .gate 38⟩,
    ⟨.sub, .gate 35, .gate 39⟩,
    ⟨.mul, .gate 5, .gate 0⟩,
    ⟨.add, .var 2, .gate 41⟩,
    ⟨.sub, .gate 2, .lit 1⟩,
    ⟨.mul, .gate 42, .gate 43⟩,
    ⟨.mul, .port 3, .gate 1⟩,
    ⟨.add, .port 2, .gate 45⟩,
    ⟨.mul, .var 0, .gate 46⟩,
    ⟨.add, .gate 44, .gate 47⟩,
    ⟨.sub, .gate 8, .gate 48⟩,
    ⟨.sub, .gate 49, .lit 1⟩,
    ⟨.mul, .gate 4, .var 11⟩,
    ⟨.mul, .gate 7, .gate 1⟩,
    ⟨.add, .gate 51, .gate 52⟩,
    ⟨.sub, .gate 53, .gate 50⟩,
    ⟨.mul, .gate 4, .gate 18⟩,
    ⟨.mul, .gate 14, .gate 54⟩,
    ⟨.add, .gate 55, .gate 56⟩,
    ⟨.mul, .gate 57, .gate 57⟩,
    ⟨.mul, .gate 4, .gate 4⟩,
    ⟨.mul, .gate 16, .gate 11⟩,
    ⟨.add, .lit 1, .gate 60⟩,
    ⟨.mul, .gate 59, .gate 61⟩,
    ⟨.sub, .gate 58, .gate 62⟩,
    ⟨.add, .lit 1, .var 3⟩,
    ⟨.mul, .gate 64, .gate 64⟩,
    ⟨.sub, .gate 65, .lit 1⟩,
    ⟨.mul, .gate 16, .gate 66⟩,
    ⟨.sub, .lit 1, .gate 67⟩,
    ⟨.mul, .gate 11, .gate 11⟩,
    ⟨.mul, .var 4, .gate 10⟩,
    ⟨.sub, .gate 70, .gate 48⟩,
    ⟨.mul, .gate 65, .gate 71⟩,
    ⟨.sub, .gate 72, .gate 10⟩,
    ⟨.add, .gate 73, .var 10⟩,
    ⟨.mul, .gate 74, .gate 74⟩,
    ⟨.mul, .gate 73, .gate 73⟩,
    ⟨.mul, .gate 67, .gate 76⟩,
    ⟨.sub, .gate 77, .lit 1⟩,
    ⟨.mul, .gate 68, .gate 75⟩,
    ⟨.add, .gate 79, .gate 78⟩,
    ⟨.mul, .gate 67, .gate 68⟩,
    ⟨.mul, .gate 69, .gate 80⟩,
    ⟨.sub, .gate 82, .gate 81⟩,
    ⟨.mul, .gate 83, .gate 83⟩,
    ⟨.mul, .gate 69, .gate 81⟩,
    ⟨.mul, .lit 4, .gate 85⟩,
    ⟨.mul, .gate 86, .gate 78⟩,
    ⟨.add, .gate 84, .gate 87⟩,
    ⟨.add, .lit 1, .gate 40⟩,
    ⟨.add, .lit 1, .gate 63⟩,
    ⟨.mul, .gate 89, .gate 90⟩,
    ⟨.add, .lit 1, .gate 88⟩,
    ⟨.mul, .gate 91, .gate 92⟩,
    ⟨.sub, .gate 93, .lit 1⟩
  ]

def lookup (p : Fin 4 → ℤ) (xs : Array (Expr (Fin 12))) : Ref → Expr (Fin 12)
  | .var j => .var j
  | .port j => .constant (p j)
  | .lit n => .constant n
  | .gate j => xs.getD j (.constant 0)

def execute (p : Fin 4 → ℤ) (xs : Array (Expr (Fin 12))) (row : Row) : Array (Expr (Fin 12)) :=
  let a := lookup p xs row.left
  let b := lookup p xs row.right
  let x := match row.op with
    | .add => a+b
    | .sub => a-b
    | .mul => a*b
  xs.push x

def retainedExpression (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  (program.foldl (execute p) #[]).getD 94 (.constant 0)

theorem row_count : program.length = 95 := rfl

/-- The internal instruction table yields the formal free-J literal, with
arbitrary integer ports; no filesystem or PDF equality is asserted. -/
theorem retained_eq_literal (p : Fin 4 → ℤ) : retainedExpression p = literal p := by
  rfl

#print axioms FreeJRetainedProgram.row_count
#print axioms FreeJRetainedProgram.retained_eq_literal
end FreeJRetainedProgram
