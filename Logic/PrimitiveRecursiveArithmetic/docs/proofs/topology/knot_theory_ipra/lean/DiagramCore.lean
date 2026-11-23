import Std

/- Host-level executable definitions. All arrays have explicit bounds,
   so these definitions also specify first-order primitive recursions.
   PD positions 0,2 are under; 1,3 are over, in counterclockwise order.
   In this convention A pairs (1,2),(3,0). -/
namespace KnotPacket

structure Diagram where
  crossings : Nat
  circles : Nat
  twin : List Nat
  deriving Repr

def dartCount (D : Diagram) : Nat := 4 * D.crossings

def twinAt (D : Diagram) (i : Nat) : Nat := D.twin[i]?.getD i

def validPairing (D : Diagram) : Bool :=
  D.twin.length == dartCount D &&
    (List.range (dartCount D)).all fun i =>
      let j := twinAt D i
      decide (j < dartCount D) && !(j == i) && twinAt D j == i

def stateMate (mask dart : Nat) : Nat :=
  let k := dart / 4
  let i := dart % 4
  let useB := mask / (2^k) % 2 == 1
  let next := if useB then i % 2 == 0 else i % 2 == 1
  4*k + (i + (if next then 1 else 3)) % 4

def iterate {α : Type} (f : α → α) (x : α) : Nat → α
  | 0 => x
  | n+1 => f (iterate f x n)

-- A breadth-first expansion with two neighbors, bounded by the dart count.
def reach (D : Diagram) (mask start : Nat) : List Bool :=
  let ix := List.range (dartCount D)
  let seed := ix.map fun j => j == start
  let step (old : List Bool) := ix.map fun j =>
    old[j]?.getD false ||
    old[(twinAt D j)]?.getD false ||
    old[(stateMate mask j)]?.getD false
  iterate step seed (dartCount D)

def stateCircles (D : Diagram) (mask : Nat) : Nat :=
  D.circles + ((List.range (dartCount D)).filter fun j =>
    let component := reach D mask j
    !((List.range j).any fun i => component[i]?.getD false)).length

def reflMod (q x y : Nat) : Nat := (2*y + q - x) % q

structure Row where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq, Repr

-- One block σ₁ σ₂⁻¹ on three Fox colors.
def block (q : Nat) (x : Row) : Row :=
  ⟨reflMod q x.b x.a, x.c, reflMod q x.a x.c⟩

def decode (q i : Nat) : Row := ⟨i % q, i / q % q, i / (q*q) % q⟩

def countClosure (q blocks : Nat) : Nat :=
  ((List.range (q^3)).filter fun i =>
    let x := decode q i
    decide (iterate (block q) x blocks = x)).length

def circle : Diagram := ⟨0, 1, []⟩
def curl : Diagram := ⟨1, 0, [1,0,3,2]⟩

example : validPairing circle = true := by decide
example : stateCircles circle 0 = 1 := by decide
example : validPairing curl = true := by decide
example : stateCircles curl 0 = 1 := by decide
example : stateCircles curl 1 = 2 := by decide
example : countClosure 3 3 = 3 := by decide
example : countClosure 5 2 = 25 := by decide

end KnotPacket
