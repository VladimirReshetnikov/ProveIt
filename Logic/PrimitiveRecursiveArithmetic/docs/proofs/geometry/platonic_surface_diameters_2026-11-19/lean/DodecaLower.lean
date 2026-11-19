import Init

/-! Exhaustive closed arithmetic certificate for the antipodal
    dodecahedron. The geometric strip-reduction lemma is proved in the text.
    This file uses Lean's kernel reduction (no native_decide). -/
namespace DodecaLower

structure Cycl where
  a : Int
  b : Int
  c : Int
  d : Int
deriving Repr, DecidableEq, Inhabited

def zero : Cycl := ⟨0,0,0,0⟩
def add (p q : Cycl) : Cycl := ⟨p.a+q.a, p.b+q.b, p.c+q.c, p.d+q.d⟩
def sub (p q : Cycl) : Cycl := ⟨p.a-q.a, p.b-q.b, p.c-q.c, p.d-q.d⟩
def neg (p : Cycl) : Cycl := sub zero p

-- z = exp(2πi/5) and z⁴ = -1-z-z²-z³.
def timesZ (p : Cycl) : Cycl := ⟨-p.d, p.a-p.d, p.b-p.d, p.c-p.d⟩

def rotate : Nat → Cycl → Cycl
  | 0, p => p
  | n+1, p => timesZ (rotate n p)

def template : List Cycl :=
  [zero, ⟨1,0,0,0⟩, ⟨1,1,0,0⟩, ⟨1,1,1,0⟩, ⟨1,1,1,1⟩]

def faces : List (List Nat) := [
  [0,16,1,14,12], [0,12,2,10,8], [0,8,4,18,16],
  [9,11,3,14,1], [16,18,5,9,1], [2,12,14,3,17],
  [17,19,6,10,2], [3,11,7,19,17], [4,13,15,5,18],
  [8,10,6,13,4], [5,15,7,11,9], [6,19,7,15,13] ]

structure Chart where
  origin : Cycl
  exponent : Nat
  negative : Bool
deriving Inhabited

def linear (k : Nat) (negative : Bool) (p : Cycl) : Cycl :=
  if negative then neg (rotate k p) else rotate k p

def point (ch : Chart) (i : Nat) : Cycl :=
  add ch.origin (linear ch.exponent ch.negative template[i]!)

-- Cross a physical edge that goes from f[e] to f[e+1] and
-- in reverse from g[l] to g[l+1]. The template directions are z^e and z^l.
def crossEdge (ch : Chart) (e l : Nat) : Chart :=
  let k := (ch.exponent + e + 5 - l) % 5
  let sign := !ch.negative
  let org := sub (point ch ((e+1)%5)) (linear k sign template[l]!)
  ⟨org, k, sign⟩

def across (f g : List Nat) (ch : Chart) : Option Chart := Id.run do
  for e in List.range 5 do
    let a := f[e]!
    let b := f[(e+1)%5]!
    let l := g.idxOf b
    if l < 5 && g[(l+1)%5]! == a then
      return some (crossEdge ch e l)
  return none

-- |sum p_i z^i|². For a difference of exponents 1, 2cos(2π/5)=φ-1;
-- for a difference 2 or 3 the corresponding doubled cosine is -φ.
def squared (p : Cycl) : Int × Int :=
  let s := p.a*p.b + p.b*p.c + p.c*p.d
  let t := p.a*p.c + p.b*p.d + p.a*p.d
  (p.a*p.a + p.b*p.b + p.c*p.c + p.d*p.d - s, s-t)

def nonnegPhi (a b : Int) : Bool :=
  let x := 2*a+b
  if b == 0 then x >= 0
  else if b > 0 then x >= 0 || 5*b*b >= x*x
  else x >= 0 && x*x >= 5*b*b

def good (q : Int × Int) : Bool := nonnegPhi (q.1-5) (q.2-7)

-- Reject an exhausted unfinished branch using the impossible square -1.
def enumerate : Nat → Nat → List Nat → Chart → List (Int × Int)
  | 0, _, _, _ => [(-1,0)]
  | n+1, i, used, ch =>
      let f := faces[i]!
      if f.contains 7 then [squared (point ch (f.idxOf 7))]
      else (List.range 12).flatMap fun j =>
        let g := faces[j]!
        if used.contains j || g.contains 0 then []
        else match across f g ch with
             | none => []
             | some next => enumerate n j (j::used) next

def result := enumerate 12 0 [0] ⟨zero,0,false⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem lowerStripCertificate :
    (result.all good && result.length == 50 && result.count (5,7) == 4) = true := by
  decide

-- Check the attaining planar segment for (0,3,10) without division.
def smul (k : Int) (p : Cycl) : Cycl := ⟨k*p.a,k*p.b,k*p.c,k*p.d⟩

def timesPhi (p : Cycl) : Cycl := neg (add (rotate 2 p) (rotate 3 p))

def stripHitsHinges : Bool := Id.run do
  let first : Chart := ⟨zero, 0, false⟩
  let some middle := across faces[0]! faces[3]! first | return false
  let some last := across faces[3]! faces[10]! middle | return false
  let q := point last (faces[10]!.idxOf 7)
  let a := point first (faces[0]!.idxOf 1)
  let b := point first (faces[0]!.idxOf 14)
  let c := point middle (faces[3]!.idxOf 9)
  let d := point middle (faces[3]!.idxOf 11)
  let t₁ := fun p => sub (smul 2 p) (timesPhi p)
  let t₂num := fun p => add (smul 2 p) (timesPhi p)
  return squared q == (5,7) &&
         t₁ q == add a (t₁ (sub b a)) &&
         t₂num q == add (smul 5 c) (t₂num (sub d c))

theorem attainingHingeCertificate : stripHitsHinges = true := by decide

def edgeNbr (i j : Nat) : Bool :=
  faces.any fun f =>
    (List.range 5).any fun k =>
      f[k]! == i && (f[(k+1)%5]! == j || f[(k+4)%5]! == j)

def reachable : Nat → List Nat
  | 0 => [0]
  | n+1 =>
    let known := reachable n
    (List.range 20).filter fun v => known.contains v || known.any (edgeNbr v)

theorem fourEdgeBall : reachable 4 = (List.range 20).erase 7 := by decide

end DodecaLower
