module
public import PA196.Literal
@[expose] public section
namespace PA196.Arithmetic.Machine.Exact
abbrev WorkingState := Fin 196
abbrev Control := Option WorkingState
def target (n : Nat) : Control := if h : n<196 then some ⟨n,h⟩ else none
structure Action where
  write : Bool
  right : Bool
  next : Control
  deriving DecidableEq, Repr
def denseLabels : List Nat := List.range 196
def row (q : WorkingState) (read : Bool) : Action :=
  let a := PA196.Literal.transition q.val read
  ⟨a.1,a.2.1,target a.2.2⟩
def start : Control := target 0
def dispatcher : Control := target 75
def halt : Control := none
def workingStates : List WorkingState := List.finRange 196
theorem working_count : workingStates.length=196 := by decide +kernel
end PA196.Arithmetic.Machine.Exact
