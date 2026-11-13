module

public import M6Data

@[expose] public section

namespace PalomarPA

/-- Look up the transition for a state and the bit under the head. -/
def machineRow (q : Nat) (b : Bool) : Option (Bool × Bool × Nat) :=
  m6Rows.findSome? fun (src, read, write, next, right) =>
    if src = q ∧ read = b.toNat then some (write != 0, right, next) else none

/-- A configuration stores the state and the two sides of the tape, nearest
cell first. The right list starts at the head. Missing cells contain zero. -/
structure TapeConfig where
  state : Nat
  left : List Bool
  right : List Bool

/-- Remove the redundant zeros at the far end of a tape side. -/
def trimTape : List Bool → List Bool
  | [] => []
  | b :: rest => if b = false ∧ trimTape rest = [] then [] else b :: trimTape rest

/-- Read and write at the head, then move one cell. A missing row ends the run. -/
def machineStep (c : TapeConfig) : Option TapeConfig :=
  match machineRow c.state (c.right.headD false) with
  | none => none
  | some (w, true, q) => some ⟨q, trimTape (w :: c.left), trimTape c.right.tail⟩
  | some (w, false, q) =>
    some ⟨q, trimTape c.left.tail, trimTape (c.left.headD false :: w :: c.right.tail)⟩

/-- Execute exactly the indicated number of steps, if they exist. -/
def machineRun : Nat → TapeConfig → Option TapeConfig
  | 0, c => some c
  | n + 1, c => (machineStep c).bind (machineRun n)

/-- The blank tape, with the machine in state zero. -/
def blank : TapeConfig := ⟨0, [], []⟩

end PalomarPA
