import Std

/-! Finite arithmetic for the skew (1,1,2) example.
Coefficient lists are in ascending order of degree. No external packages. -/

namespace QuarticCertificate

def coeff : List Int :=
  [613884455156800, -209597886831520, 26061786638084, -1382740019876, 25856961601]

def P : List Int := [5, -7, 2, 0, 1]
def R : List Int := [-8, 4, -3, 5]

theorem monicReduction :
    (25856961601 : Int) % 17 = 4 ∧ (4*13 : Int) % 17 = 1 ∧
    coeff.map (fun a => (13*a)%17) = P.map (fun a => a%17) := by decide

structure Residue where
  c₀ : Int
  c₁ : Int
  c₂ : Int
  c₃ : Int
  deriving DecidableEq, Repr

/-- Multiply by X and substitute X^4 = -5 + 7X - 2X^2. -/
def timesX : Residue → Residue
  | ⟨a,b,c,d⟩ => ⟨(-5*d)%17, (a+7*d)%17, (b-2*d)%17, c%17⟩

def xPower : Nat → Residue
  | 0 => ⟨1,0,0,0⟩
  | k+1 => timesX (xPower k)

def subtractX (r : Residue) : List Int := [r.c₀, (r.c₁-1)%17, r.c₂, r.c₃]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem powerRemainder : subtractX (xPower 289) = R.map (fun a => a%17) := by decide

def convolutionAt (A B : List Int) (k : Nat) : Int :=
  ((List.range (k+1)).map fun j => A[j]?.getD 0 * B[k-j]?.getD 0).sum

/-- Both integer products have degree at most six, so this covers all coefficients. -/
theorem bezoutCoefficients :
    ((List.range 7).map fun k =>
      (convolutionAt [0,-8,5] P k + convolutionAt [2,-4,1,-1] R k)%17)
       = [1,0,0,0,0,0,0] := by decide

/-- Horner update modulo X^2 + aX + b. A remainder is stored (constant, linear). -/
def quadraticRem (a b : Int) : Int × Int :=
  P.foldr (fun c r => ((c-b*r.2)%17, (r.1-a*r.2)%17)) (0,0)

def valueMod (x : Int) : Int := P.foldr (fun c r => (c+x*r)%17) 0

set_option maxRecDepth 10000 in
theorem noLinearOrQuadratic :
    ((List.range 17).all fun a => valueMod a != 0) = true ∧
    ((List.range 17).all fun a => (List.range 17).all fun b =>
      quadraticRem a b != (0,0)) = true := by decide

/-- Numerator of d^4 * F(n/d). -/
def evalScaled (n d : Int) : Int :=
  ((List.range 5).map fun i => coeff[i]?.getD 0 * n^i * d^(4-i)).sum

theorem rootBracket :
    0 < evalScaled 457633 50000 ∧ evalScaled 228817 25000 < 0 := by decide

/-- Upper bound for d^3 F'(t) on [l/d,h/d], using monomial signs. -/
def derivativeUpper (l h d : Int) : Int :=
  4 * (coeff[4]?.getD 0) * h^3 + 3 * (coeff[3]?.getD 0) * l^2 * d +
  2 * (coeff[2]?.getD 0) * h * d^2 + (coeff[1]?.getD 0) * d^3

theorem derivativeUpperNegative : derivativeUpper 915266 915268 100000 < 0 := by decide

end QuarticCertificate
