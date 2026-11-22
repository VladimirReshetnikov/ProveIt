import Std

/-! Integer support and tree replay. Input balls enclose the developed
point or the gate sample at the parameter prescribed by its position in
the tree. Their analytic enclosure and the curvature bound are separate
hypotheses. No square root or floating-point operation is trusted here. -/
namespace Oloid.Replay

def scale : Nat := 100000000000000

structure Ball where
  x : Int
  y : Int
  r : Nat
deriving Inhabited

structure Cell where
  a : Ball
  b : Ball
  curved : Bool
  level : Nat
  index : Nat
deriving Inhabited

structure Direction where
  x : Int
  y : Int
  diffBound : Nat

inductive Cert where
  | leaf (dirs : List Direction)
  | split (middle : Ball) (left right : Cert)
  | inside

def pt (b : Ball) : Cell := ⟨b,b,false,0,0⟩

def radius (c : Cell) : Nat :=
  let denominator := 8 * 4^c.level
  max c.a.r c.b.r + if c.curved then (5*scale+denominator-1)/denominator else 0

def sqn (x y : Int) : Int := x*x+y*y

def supportSum (px py : Int) : List Cell → List Direction → Option Int
  | [], [] => if px==0 && py==0 then some 0 else none
  | c :: cs, u :: us =>
    let dx := px-u.x
    let dy := py-u.y
    let h : Int := u.diffBound
    if sqn u.x u.y > (scale*scale : Nat) || sqn dx dy > h*h then none
    else
      let term := min (dx*c.a.x+dy*c.a.y) (dx*c.b.x+dy*c.b.y) - h*radius c
      (supportSum u.x u.y cs us).map (term+·)
  | _, _ => none

def leafOK (p q : Ball) (cells : List Cell) (threshold : Nat) (u : List Direction) : Bool :=
  match supportSum 0 0 (pt p :: cells ++ [pt q]) u with
  | none => false
  | some lower => decide (lower ≥ (threshold*scale : Nat))

def contained (c : Cell) (range : Nat × Nat × Nat) : Bool :=
  let (lo,hi,den) := range
  let scaleTwo := 2^c.level
  den>0 && lo*scaleTwo ≤ c.index*den && (c.index+1)*den ≤ hi*scaleTwo

def verifyWith (p q : Ball) (threshold : Nat) (region : List (Nat × Nat × Nat)) : Cert → List Cell → Bool
  | .inside, cells => !region.isEmpty && cells.length == region.length &&
      (List.zipWith contained cells region).all id
  | .leaf u, cells => leafOK p q cells threshold u
  | .split mid l r, cells =>
    if cells.isEmpty then false else
    let i := if cells.length == 2 && (cells.getD 1 default).level < (cells.getD 0 default).level then 1 else 0
    let c := cells.getD i default
    verifyWith p q threshold region l (cells.set i {c with b := mid, level := c.level+1, index := 2*c.index}) &&
      verifyWith p q threshold region r (cells.set i {c with a := mid, level := c.level+1, index := 2*c.index+1})

def verifyTree (p q : Ball) (threshold : Nat) : Cert → List Cell → Bool :=
  verifyWith p q threshold []

def upperSum (a : Ball) : List Ball → List Nat → Option Nat
  | [], [] => some 0
  | b::bs, n::ns =>
    if sqn (a.x-b.x) (a.y-b.y) ≤ (n*n : Nat) then
      (upperSum b bs ns).map (n+a.r+b.r+·)
    else none
  | _, _ => none

def upperOK (p : Ball) (rest : List Ball) (n : List Nat) (bound : Nat) : Bool :=
  match upperSum p rest n with
  | none => false
  | some k => decide (k ≤ bound)

end Oloid.Replay
