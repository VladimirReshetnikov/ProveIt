import MoserWorm.Common.Interval.Basic

/-! Closed dyadic boxes and binary subdivision certificates. -/

namespace MoserWorm

variable {n : Nat}

abbrev DyadicBox (n : Nat) := Vector DIval n

namespace DyadicBox

def midpoint (a : DIval) : Int := a.lo + (a.hi - a.lo) / 2

def left (box : DyadicBox n) (axis : Fin n) : DyadicBox n :=
  box.set axis.val ⟨box[axis].lo, midpoint box[axis]⟩ axis.isLt

def right (box : DyadicBox n) (axis : Fin n) : DyadicBox n :=
  box.set axis.val ⟨midpoint box[axis], box[axis].hi⟩ axis.isLt

def valid (box : DyadicBox n) : Bool :=
  box.toArray.all fun a => a.lo ≤ a.hi

end DyadicBox

/-- Leaves carry witnesses; each branch covers both halves of its parent box. -/
inductive BoxTree (n : Nat) (α : Type) where
  | leaf (witness : α)
  | split (axis : Fin n) (left right : BoxTree n α)
  deriving Repr

namespace BoxTree

variable {α : Type}

def check (checkLeaf : DyadicBox n → α → Bool) :
    DyadicBox n → BoxTree n α → Bool
  | box, .leaf witness => checkLeaf box witness
  | box, .split axis left right =>
      check checkLeaf (box.left axis) left &&
      check checkLeaf (box.right axis) right

theorem check_split {checkLeaf : DyadicBox n → α → Bool} {box : DyadicBox n}
    {axis : Fin n} {left right : BoxTree n α}
    (hl : check checkLeaf (box.left axis) left = true)
    (hr : check checkLeaf (box.right axis) right = true) :
    check checkLeaf box (.split axis left right) = true :=
  (congrArg (fun b => b && check checkLeaf (box.right axis) right) hl).trans
    (congrArg (fun b => true && b) hr)

def leafCount : BoxTree n α → Nat
  | .leaf _ => 1
  | .split _ left right => left.leafCount + right.leafCount

end BoxTree

end MoserWorm
