import Std

namespace IPRAComplexity

/-- An assignment is an ambient interface; finite encodings replace it in iPRA. -/
abbrev Assignment := Nat → Bool

structure Literal where
  index : Nat
  positive : Bool
  deriving DecidableEq, Repr

def Literal.eval (a : Assignment) (l : Literal) : Bool :=
  if l.positive then a l.index else !(a l.index)

abbrev Clause := List Literal
abbrev CNF := List Clause

def Clause.eval (a : Assignment) (c : Clause) : Bool :=
  c.foldr (fun l b => l.eval a || b) false

def CNF.eval (a : Assignment) (f : CNF) : Bool :=
  f.foldr (fun c b => c.eval a && b) true

def pos (v : Nat) : Literal := ⟨v, true⟩
def neg (v : Nat) : Literal := ⟨v, false⟩

/-- Clauses expressing z = (x AND y); all clauses have at most three literals. -/
def andClauses (x y z : Nat) : CNF :=
  [[neg z, pos x], [neg z, pos y], [pos z, neg x, neg y]]

/-- Clauses expressing z = NOT x. -/
def notClauses (x z : Nat) : CNF :=
  [[pos z, pos x], [neg z, neg x]]

def constClauses (b : Bool) (z : Nat) : CNF :=
  [[⟨z, b⟩]]

theorem andClauses_correct (a : Assignment) (x y z : Nat) :
    CNF.eval a (andClauses x y z) = true ↔ a z = (a x && a y) := by
  cases hx : a x <;> cases hy : a y <;> cases hz : a z <;>
    simp [andClauses, CNF.eval, Clause.eval, Literal.eval, pos, neg, hx, hy, hz]

theorem notClauses_correct (a : Assignment) (x z : Nat) :
    CNF.eval a (notClauses x z) = true ↔ a z = !(a x) := by
  cases hx : a x <;> cases hz : a z <;>
    simp [notClauses, CNF.eval, Clause.eval, Literal.eval, pos, neg, hx, hz]

theorem constClauses_correct (a : Assignment) (b : Bool) (z : Nat) :
    CNF.eval a (constClauses b z) = true ↔ a z = b := by
  cases b <;> cases hz : a z <;>
    simp [constClauses, CNF.eval, Clause.eval, Literal.eval, hz]

theorem CNF.eval_append (a : Assignment) (f g : CNF) :
    CNF.eval a (f ++ g) = (CNF.eval a f && CNF.eval a g) := by
  induction f with
  | nil => simp [CNF.eval]
  | cons c f ih => simp [CNF.eval] at ih ⊢; rw [ih]; cases c.eval a <;> rfl

/-- A straight-line Boolean gate whose input wire numbers are explicit. -/
inductive Gate where
  | constant : Bool → Gate
  | negate : Nat → Gate
  | conjunction : Nat → Nat → Gate
  deriving Repr

def Gate.eval (a : Assignment) : Gate → Bool
  | .constant b => b
  | .negate x => !(a x)
  | .conjunction x y => a x && a y

def Gate.clauses (z : Nat) : Gate → CNF
  | .constant b => constClauses b z
  | .negate x => notClauses x z
  | .conjunction x y => andClauses x y z

theorem Gate.clauses_correct (a : Assignment) (z : Nat) (g : Gate) :
    CNF.eval a (g.clauses z) = true ↔ a z = g.eval a := by
  cases g with
  | constant b => exact constClauses_correct a b z
  | negate x => exact notClauses_correct a x z
  | conjunction x y => exact andClauses_correct a x y z

/-- The gate-output variable is stored explicitly, for finite constraint compilation. -/
abbrev GateSystem := List (Nat × Gate)

def GateSystem.clauses : GateSystem → CNF
  | [] => []
  | (z, g) :: gs => g.clauses z ++ GateSystem.clauses gs

def GateSystem.satisfies (a : Assignment) : GateSystem → Prop
  | [] => True
  | (z, g) :: gs => a z = g.eval a ∧ GateSystem.satisfies a gs

theorem GateSystem.clauses_correct (a : Assignment) (gs : GateSystem) :
    CNF.eval a gs.clauses = true ↔ gs.satisfies a := by
  induction gs with
  | nil => simp [clauses, CNF.eval, satisfies]
  | cons zg gs ih =>
    rcases zg with ⟨z, g⟩
    simp only [clauses, CNF.eval_append, Bool.and_eq_true,
      Gate.clauses_correct, ih, satisfies]

/-- The local gate compiler produces only clauses of width at most three. -/
theorem Gate.clauses_width (g : Gate) (z : Nat) :
    ∀ c ∈ g.clauses z, c.length ≤ 3 := by
  cases g <;>
    simp [Gate.clauses, constClauses, notClauses, andClauses] <;> decide

theorem Gate.clauses_count (g : Gate) (z : Nat) :
    (g.clauses z).length ≤ 3 := by
  cases g <;> simp [Gate.clauses, constClauses, notClauses, andClauses]

theorem GateSystem.clauses_count (gs : GateSystem) :
    gs.clauses.length ≤ 3 * gs.length := by
  induction gs with
  | nil => simp [clauses]
  | cons zg gs ih =>
    rcases zg with ⟨z, g⟩
    simp only [clauses, List.length_append, List.length_cons]
    have h := g.clauses_count z
    omega

end IPRAComplexity
