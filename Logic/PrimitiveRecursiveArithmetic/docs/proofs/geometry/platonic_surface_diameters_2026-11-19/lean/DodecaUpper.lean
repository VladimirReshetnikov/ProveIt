import DodecaLower

namespace DodecaUpper
open DodecaLower
abbrev K := Int × Int

def ksub (p q : K) : K := (p.1-q.1, p.2-q.2)
def kadd (p q : K) : K := (p.1+q.1, p.2+q.2)
def kmul (p q : K) : K :=
  (p.1*q.1+p.2*q.2, p.1*q.2+p.2*q.1+p.2*q.2)
def nn (p : K) : Bool := nonnegPhi p.1 p.2

-- Oriented area divided by sin(2π/5), computed in Z[φ].
def det (p q : Cycl) : K :=
  let r := p.a*q.b-p.b*q.a + p.b*q.c-p.c*q.b + p.c*q.d-p.d*q.c
  let s := p.a*q.c-p.c*q.a + p.b*q.d-p.d*q.b - (p.a*q.d-p.d*q.a)
  (r-s,s)

def crossings (s t : Cycl) (hinges : List (Cycl × Cycl)) : Bool := Id.run do
  let delta := sub t s
  let mut prevN : K := (0,0)
  let mut prevD : K := (1,0)
  for (a,b) in hinges do
    let edge := sub b a
    let den := det delta edge
    if den == (0,0) then return false
    let positive := fun x => if nn den then x else ksub (0,0) x
    let n := positive (det (sub a s) edge)
    let h := positive (det (sub a s) delta)
    let d := positive den
    if !(nn n && nn (ksub d n) && nn h && nn (ksub d h) &&
         nn (ksub (kmul n prevD) (kmul prevN d))) then return false
    prevN := n
    prevD := d
  return true

def physical (ch : Chart) (face v : Nat) : Cycl := point ch (faces[face]!.idxOf v)
def hinge (ch : Chart) (face a b : Nat) : Cycl × Cycl :=
  (smul 10 (physical ch face a),smul 10 (physical ch face b))
def corners (ch : Chart) (face a b : Nat) : List Cycl :=
  [smul 10 (physical ch face a),
   smul 5 (add (physical ch face a) (physical ch face b)),
   smul 2 (((List.range 5).map (point ch)).foldl add zero)]

def check : Bool := Id.run do
  let c₀ : Chart := ⟨zero,0,false⟩
  let some c₂ := across faces[0]! faces[2]! c₀ | return false
  let some c₈ := across faces[2]! faces[8]! c₂ | return false
  let some c₁₁ := across faces[8]! faces[11]! c₈ | return false
  let hinges := [hinge c₀ 0 0 16, hinge c₂ 2 4 18, hinge c₈ 8 13 15]
  let s := corners c₀ 0 0 16
  let t := corners c₁₁ 11 7 19
  let d := fun (i j : Nat) => squared (sub s[i]! t[j]!)
  let mut gaps : List K := []
  for i in List.range 3 do
    for j in List.range 3 do
      if !(crossings s[i]! t[j]! hinges) then return false
      gaps := gaps ++ [ksub (1000,1400) (kadd (d i j) (d j i))]
  return gaps == [(0,0),(50,50),(20,60),(50,50),(100,50),(70,10),
                  (20,60),(70,10),(80,40)]

theorem ninePairsAndThreeHinges : check = true := by decide
end DodecaUpper
