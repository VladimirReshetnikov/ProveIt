module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAMachine
@[expose] public section

namespace PA196.Arithmetic.Machine

/-- A bi-infinite binary tape. False is blank. -/
abbrev Tape := Int → Bool

structure Configuration where
  control : Control
  head : Int
  tape : Tape

/-- Write at the current cell before moving. -/
def writeTape (t : Tape) (p : Int) (b : Bool) : Tape :=
  fun i => if i = p then b else t i

def step (c : Configuration) : Option Configuration :=
  match c.control with
  | none => none
  | some q =>
    let a := row q (c.tape c.head)
    some ⟨a.next, c.head + (if a.right then 1 else -1), writeTape c.tape c.head a.write⟩

def run : Nat → Configuration → Option Configuration
  | 0, c => some c
  | n + 1, c => (step c).bind (run n)

def blank : Configuration := ⟨start, 0, fun _ => false⟩

def Halts (c : Configuration) : Prop :=
  ∃ n c', run n c = some c' ∧ c'.control = halt

/-- The literal blank start makes a single write-right transition. -/
theorem blank_first_step : step blank =
    some ⟨target 1, 1, writeTape (fun _ => false) 0 true⟩ := rfl

theorem halt_no_step (p : Int) (t : Tape) : step ⟨halt, p, t⟩ = none := rfl

end PA196.Arithmetic.Machine

