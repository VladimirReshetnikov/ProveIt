import Arithmetic
import FiniteSearch

/-!
Executable data definitions and explicitly named, unproved target propositions.
There are no declarations postulating these targets.  `RungeCertificate` checks
the polynomial identity coefficient by coefficient; it contains no height bound.
This file is a native specification layer, not an embedded iPRA derivation.
-/
namespace SiegelIPRA

abbrev ZPolynomial := List Int

/-- Coefficients are in ascending degree order. -/
def polyEval : ZPolynomial → Int → Int
  | [], _ => 0
  | a :: as, x => a + x * polyEval as x

def polyCoeff (f : ZPolynomial) (i : Nat) : Int := f[i]?.getD 0

def polyNorm (f : ZPolynomial) : Nat :=
  (f.map Int.natAbs).foldl (· + ·) 0

def convolutionCoeff (a : ZPolynomial) (i : Nat) : Int :=
  ((List.range (i+1)).map fun j => polyCoeff a j * polyCoeff a (i-j)).foldl (· + ·) 0

structure RungeData where
  f : ZPolynomial
  a : ZPolynomial
  r : ZPolynomial
  denominator : Nat
  deriving Repr

def certificateLength (c : RungeData) : Nat :=
  max c.f.length (max (2*c.a.length) c.r.length)

/-- Executable finite check: D² f=A²+R, deg R<deg A, R nonzero. -/
def certificateCheck (c : RungeData) : Bool :=
  decide (0 < c.denominator) &&
  decide (2 ≤ c.a.length) &&
  (polyCoeff c.a (c.a.length-1) != 0) &&
  decide (c.r.length < c.a.length) &&
  (c.r.any fun z => z != 0) &&
  (List.range (certificateLength c)).all fun i =>
    (c.denominator : Int)*(c.denominator : Int)*polyCoeff c.f i ==
      convolutionCoeff c.a i + polyCoeff c.r i

def RungeCertificate (c : RungeData) : Prop := certificateCheck c = true

def xBound (c : RungeData) : Nat :=
  polyNorm (c.a.take (c.a.length-1)) + polyNorm c.r

def yBound (c : RungeData) : Nat :=
  ((c.f.zipIdx).map fun (a,i) => a.natAbs * (max 1 (xBound c))^i).foldl (· + ·) 0

def IsPoint (f : ZPolynomial) (x y : Int) : Prop :=
  y*y = polyEval f x

/-- Target proved in the paper, not yet proved for polynomial lists in Lean. -/
def RungeBoundTarget : Prop :=
  ∀ c : RungeData, RungeCertificate c →
    ∀ x y : Int, IsPoint c.f x y →
      x.natAbs ≤ xBound c ∧ y.natAbs ≤ yBound c

def integerInterval (B : Nat) : List Int :=
  (List.range (2*B+1)).map fun (i : Nat) => (i : Int) - (B : Int)

def boxPoints (f : ZPolynomial) (Bx By : Nat) : List (Int × Int) :=
  (integerInterval Bx).flatMap fun x =>
    ((integerInterval By).filter fun y => y*y == polyEval f x).map fun y => (x,y)

def RungeEnumerationTarget : Prop :=
  ∀ c : RungeData, RungeCertificate c →
    ∀ x y : Int, IsPoint c.f x y ↔
      (x,y) ∈ boxPoints c.f (xBound c) (yBound c)

def genusFamily (m : Nat) : ZPolynomial :=
  [1,1] ++ List.replicate (2*m-2) 0 ++ [1]

def GenusFamilyTarget : Prop :=
  ∀ m : Nat, 2 ≤ m → ∀ x y : Int,
    IsPoint (genusFamily m) x y ↔
      (x = -1 ∨ x = 0) ∧ (y = -1 ∨ y = 1)

structure Monomial where
  coefficient : Int
  exponents : List Nat
  deriving Repr

abbrev MultivariatePolynomial := List Monomial

def monomialEval (t : Monomial) (xs : List Int) : Int :=
  t.coefficient * ((xs.zip t.exponents).map fun (x,e) => x^e).foldl (· * ·) 1

def multivariateEval (f : MultivariatePolynomial) (xs : List Int) : Int :=
  (f.map fun t => monomialEval t xs).foldl (· + ·) 0

structure AffineSystem where
  dimension : Nat
  equations : List MultivariatePolynomial
  deriving Repr

def systemWellFormed (c : AffineSystem) : Bool :=
  c.equations.all fun f => f.all fun t => t.exponents.length == c.dimension

def integralPointTest (c : AffineSystem) (xs : List Int) : Bool :=
  systemWellFormed c && xs.length == c.dimension &&
    c.equations.all fun f => multivariateEval f xs == 0

def coordinateHeight (xs : List Int) : Nat :=
  (xs.map Int.natAbs).foldl max 0

/-- `admissible` must independently mean smooth positive-genus affine curve.
Its geometric implementation and coverage are remaining tasks, not assumptions
proved by this definition. The full height target itself is not proved here. -/
def PositiveSiegelTarget (admissible : AffineSystem → Bool) : Prop :=
  ∀ c, admissible c = true → ∃ B : Nat,
    ∀ xs, integralPointTest c xs = true → coordinateHeight xs ≤ B

/-- Constructive bound on cardinality, a different unproved general target. -/
def CountSiegelTarget (admissible : AffineSystem → Bool) : Prop :=
  ∀ c, admissible c = true → ∃ N : Nat,
    ∀ pts : List (List Int),
      (pts.all fun xs => integralPointTest c xs) = true → pts.Nodup →
        pts.length ≤ N

def sampleCertificate : RungeData :=
  { f := [1,1,0,0,1], a := [0,0,1], r := [1,1], denominator := 1 }

theorem sample_certificate_valid : RungeCertificate sampleCertificate := by
  change certificateCheck sampleCertificate = true
  decide

#eval xBound sampleCertificate
#eval boxPoints sampleCertificate.f 2 8

end SiegelIPRA
