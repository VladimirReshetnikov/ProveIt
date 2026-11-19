import FiniteRoutes

/-! A uniform primitive-recursive observation of the 45 exact lengths.
Finite arithmetic only. The error proof is in the accompanying report.
The fast high-precision certificate replay is a separate algorithm. -/
namespace Oloid.Observer

abbrev Point := Rat × Rat

def add (p q : Point) : Point := (p.1+q.1, p.2+q.2)
def sub (p q : Point) : Point := (p.1-q.1, p.2-q.2)
def smul (s : Rat) (p : Point) : Point := (s*p.1,s*p.2)

/-- Floor of M sqrt(x) for rational x≥0 and positive natural M. -/
def rootIndex (x : Rat) (M : Nat) : Nat :=
  (x.num.toNat*M*M/x.den).sqrt

def root (x : Rat) (M : Nat) : Rat := (rootIndex x M : Rat) / (M : Rat)

def floorTo (x : Rat) (M : Nat) : Rat :=
  (((M : Rat)*x).floor : Rat) / (M : Rat)

def velocity (M : Nat) (r : Rat) (i : Nat) : Point :=
  let u := (i : Rat)/(M : Rat)
  let b := u*u
  let t := 1-b
  let d := (1+3*b)*(1+3*b)
  let k := 2*r/d
  (floorTo (k*t*root t M) M, floorTo (k*u*(3+b)) M)

structure Atlas where
  size : Nat
  ar : Array Point
  r : Rat
  corner : Point
  ctr : Point

/-- ar[k] approximates a(k/M). Quantizing every summand keeps its
denominator bounded by M² after integration. -/
def atlas (M : Nat) : Atlas := Id.run do
  let r := root 3 M
  let mut out : Array Point := #[(0,0)]
  let mut curr : Point := (0,0)
  for i in [:M] do
    curr := add curr (smul (1/(M : Rat)) (velocity M r i))
    out := out.push curr
  return ⟨M,out,r,curr,add curr (0,r)⟩

structure Sample where
  h : Rat
  s : Rat
  y : Bool
  z : Bool
  deriving Inhabited

def samples : Array Sample := #[
  ⟨1/5, 1/6, true, true⟩, ⟨9/10, 7/10, true, true⟩,
  ⟨3/2, 2/5, true, false⟩, ⟨1/2, 3/11, true, false⟩,
  ⟨7/6, 1/8, false, true⟩, ⟨2/3, 11/13, false, true⟩,
  ⟨4/3, 8/11, false, false⟩, ⟨1/3, 4/7, false, false⟩,
  ⟨1, 5/9, true, true⟩, ⟨7/8,19/20,false,true⟩]

def pt (a : Atlas) (s : Sample) : Point :=
  let h2 := s.h*s.h
  let ka := rootIndex (h2/3) a.size
  let kb := rootIndex ((3-h2)/(3*(1+h2))) a.size
  let x := a.ar[ka]?.getD (0,0)
  let y := sub a.ctr (a.ar[kb]?.getD (0,0))
  add (smul (1-s.s) x) (smul s.s y)

inductive Gate where | A | B | L | R
  deriving Repr

def gate (a : Atlas) (g : Gate) (N i : Nat) : Point :=
  let x := a.ar[a.size*i/N]?.getD (0,0)
  let t := (i : Rat)/(N : Rat)
  match g with
  | .A => x
  | .B => sub a.ctr x
  | .L => (0,t*a.r)
  | .R => add a.corner (0,t*a.r)

def chord (a : Atlas) (p q : Point) : Nat :=
  let (x,y) := sub p q
  rootIndex (x*x+y*y) a.size

inductive Word where
  | direct
  | one (g : Gate)
  | two (g h : Gate)
  deriving Repr

def words (p q : Sample) : List Word :=
  match (p.y != q.y), (p.z != q.z) with
  | false,false => [.direct]
  | true,false => [.one .B,.one .L]
  | false,true => [.one .A,.one .R]
  | true,true => [.two .B .A,.two .B .R,.two .L .A,.two .L .R,
                  .two .A .B,.two .R .B,.two .A .L,.two .R .L]

def wordCost (a : Atlas) (N : Nat) (p q : Point) : Word → Nat
  | .direct => chord a p q
  | .one g => Finite.minCost (fun i =>
      let x := gate a g N i
      chord a p x + chord a x q) N
  | .two g h => Finite.meshCost (fun i j =>
      let x := gate a g N i
      let y := gate a h N j
      chord a p x + chord a x y + chord a y q) N

/-- For p,q from the table the result is within 2^(-n) of the distance.
Use mesh N dividing M. The lower and upper error estimates differ. -/
def observe (p q : Sample) (n : Nat) : Rat :=
  let N := 2^(n+6)
  let M := 2^(n+12)
  let a := atlas M
  let costs := (words p q).map (wordCost a N (pt a p) (pt a q))
  let c : Nat := match costs with
    | [] => 0
    | h::t => t.foldl min h
  (c : Rat)/(M : Rat)

#guard rootIndex (9/16) 8 == 6
example : (words samples[0]! samples[1]!).length = 1 := by decide
example : (words samples[0]! samples[6]!).length = 8 := by decide

end Oloid.Observer
