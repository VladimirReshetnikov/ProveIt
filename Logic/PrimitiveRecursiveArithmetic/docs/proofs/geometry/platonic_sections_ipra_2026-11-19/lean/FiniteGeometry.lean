import Mathlib

/-!
Outline / implementation starting point, NOT compiled in this environment.
This file defines the mathematical finite data. It is not an iPRA proof term.
IPRAEndpoints.lean states the separate object-language endpoint interface.
-/

namespace PlatonicSections

/-- A rational coefficient pair for a + b*phi, phi^2=phi+1. -/
structure Gold where
  a : ℚ
  b : ℚ
  deriving DecidableEq, Repr

namespace Gold
def add (x y : Gold) : Gold := ⟨x.a+y.a, x.b+y.b⟩
def neg (x : Gold) : Gold := ⟨-x.a,-x.b⟩
def mul (x y : Gold) : Gold :=
  ⟨x.a*y.a+x.b*y.b, x.a*y.b+x.b*y.a+x.b*y.b⟩
def norm (x : Gold) : ℚ := x.a^2+x.a*x.b-x.b^2
def inv (x : Gold) : Gold := ⟨(x.a+x.b)/norm x,-x.b/norm x⟩
def qsign (q : ℚ) : ℤ := if q>0 then 1 else if q<0 then -1 else 0
def sign (x : Gold) : ℤ :=
  let c := 2*x.a+x.b
  let d := x.b
  if d=0 then qsign c else
  if c=0 then qsign d else
  if qsign c=qsign d then qsign c else qsign c*qsign (c^2-5*d^2)
def le (x y : Gold) : Prop := sign (add y (neg x)) ≥ 0
def phi : Gold := ⟨0,1⟩
end Gold

abbrev V3 (K : Type*) := Fin 3 → K

section Vector
variable {K : Type*} [CommRing K]
def vzero : V3 K := fun _ => 0
def vadd (p q : V3 K) : V3 K := fun i => p i+q i
def vsub (p q : V3 K) : V3 K := fun i => p i-q i
def vscale (a : K) (p : V3 K) : V3 K := fun i => a*p i
def dot (p q : V3 K) : K := p 0*q 0+p 1*q 1+p 2*q 2
def cross (p q : V3 K) : V3 K :=
  ![p 1*q 2-p 2*q 1, p 2*q 0-p 0*q 2, p 0*q 1-p 1*q 0]
def plane (n : V3 K) (t : K) (p : V3 K) : Prop := dot n p=t
def doubleAreaVector (ps : List (V3 K)) : V3 K :=
  (ps.zip (ps.drop 1 ++ ps.take 1)).foldl
    (fun w e => vadd w (cross e.1 e.2)) vzero
end Vector

section Area
variable {K : Type*} [Field K]
def areaSq (ps : List (V3 K)) : K :=
  let w := doubleAreaVector ps
  dot w w/4
def edgeIntersection (n : V3 K) (t : K) (p q : V3 K) : V3 K :=
  let hp := dot n p-t
  let hq := dot n q-t
  vscale (hp-hq)⁻¹ (vsub (vscale hp q) (vscale hq p))
end Area

/-- Sparse polynomial data for a fixed three-variable coefficient certificate. -/
structure Term3 (K : Type*) where
  coeff : K
  i : ℕ
  j : ℕ
  k : ℕ

section Polynomial
variable {K : Type*} [CommSemiring K]
def monomial (t : Term3 K) (x y z : K) : K := x^t.i*y^t.j*z^t.k
def evalPoly : List (Term3 K) → K → K → K → K
  | [], _, _, _ => 0
  | t::ts, x, y, z => t.coeff*monomial t x y z+evalPoly ts x y z
end Polynomial

section ExplicitIdentities
variable {K : Type*} [CommRing K]

theorem cubeSlack (r : K) :
    2*(1+r)^4-(2+r^2)*(1+2*r)^2 = r^2*(3+4*r-2*r^2) := by ring

theorem cubeSlackNonnegativeForm (r : K) :
    3+4*r-2*r^2 = 3+2*r+2*r*(1-r) := by ring

theorem octaSlack (a b c : K) :
    ((a+b)*(a+c)*(b+c))^2-(a^2+b^2+c^2)*(a*b+a*c+b*c)^2 =
      2*(a^3*b^3+a^3*c^3+b^3*c^3) +
      4*a*b*c*(a^2*b+a^2*c+a*b^2+a*c^2+b^2*c+b*c^2) +
      7*a^2*b^2*c^2 := by ring

theorem tetraSlack (a b c d : K) :
    1-((a+d-a*d-c*d)+(b+c-b*c-c*d)-(a*b-c*d)) =
      (a+c-1)*(b+d-1) := by ring

end ExplicitIdentities

/-!
To complete the formalization, implement and prove, in this order:

1. Gold field/order laws and the code-to-Gold interpretation.
2. Exact clipping and monotone-chain hull; section completeness.
3. Vector shoelace and finite vertical-trapezoid additivity/monotonicity.
4. The reflected-fiber construction and CS1--CS5 in the report.
5. Finite reflection-orbit maximum and the explicit ray-cone covers.
6. Area-formula cross-multiplication and denominator positivity, including
   the exceptional middle dodecahedral ray and the icosahedral axis.
7. Sparse coefficient identity checking and nonnegative evaluation.
8. Exact witnesses, homothety, and the stated sharp comparison.

The executable algorithms and exact polynomial tables are in ../code and
../certificates. No `axiom` or `sorry` in this file asserts an unproved
global geometry result. This list is a work plan, not a completed proof.
-/

end PlatonicSections
