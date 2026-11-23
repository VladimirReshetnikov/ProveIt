import Mathlib

/-!
# Explicit finite analytic programs for the report

STATUS: uncompiled definitions only. No correctness theorem is asserted here.
The definitions implement the exact formulas and schedules in the report;
their iPRA correctness is to be proved by the finite-loop/observation bridges.

Fin d -> Q is finite vector data. Higher-order parameters used below denote
fixed finite tables or fixed metatheoretic program families; no such parameter
is quantified over inside first-order iPRA and no arbitrary PR evaluator occurs.
-/

namespace AnalyticGeometryIPRA.AnalyticPrograms

open scoped BigOperators

/-- Sparse polynomial data. Repeated exponents and zero coefficients are allowed. -/
structure Monomial (d : ℕ) where
  coefficient : ℚ
  exponent : Fin d → ℕ

abbrev PolynomialData (d : ℕ) := List (Monomial d)

def degree {d : ℕ} (a : Monomial d) : ℕ := ∑ i, a.exponent i

def monomialValue {d : ℕ} (a : Monomial d) (x : Fin d → ℚ) : ℚ :=
  a.coefficient * ∏ i, (x i)^(a.exponent i)

def polyValue {d : ℕ} (p : PolynomialData d) (x : Fin d → ℚ) : ℚ :=
  (p.map (fun a => monomialValue a x)).sum

/-- When the exponent is zero, the coefficient is zero; the truncated new
exponent therefore causes no spurious constant term. -/
def partialMonomial {d : ℕ} (i : Fin d) (a : Monomial d) : Monomial d :=
  ⟨a.coefficient*(a.exponent i : ℚ),
   Function.update a.exponent i (a.exponent i-1)⟩

def formalPartial {d : ℕ} (i : Fin d) (p : PolynomialData d) : PolynomialData d :=
  p.map (partialMonomial i)

def gradientValue {d : ℕ} (p : PolynomialData d) (x : Fin d → ℚ) : Fin d → ℚ :=
  fun i => polyValue (formalPartial i p) x

/-- H, B, L are exactly the report's coefficient bounds; M >= 1 is a theorem guard. -/
def H {d : ℕ} (p : PolynomialData d) (M : ℕ) : ℚ :=
  (p.map (fun a => |a.coefficient|*((M:ℚ)+1)^(degree a))).sum

def B {d : ℕ} (p : PolynomialData d) (M : ℕ) : ℚ :=
  1+(p.map (fun a => |a.coefficient|*(degree a:ℚ)*((M:ℚ)+1)^(degree a))).sum

def L {d : ℕ} (p : PolynomialData d) (M : ℕ) : ℚ :=
  1+(p.map (fun a => |a.coefficient|*(degree a:ℚ)^2*((M:ℚ)+1)^(degree a))).sum

def inBox {d : ℕ} (x center : Fin d → ℚ) (radius : ℚ) : Prop :=
  ∀ i, |x i-center i| ≤ radius

/-- Least j <= C such that C <= 2^j; the fallback totalizes invalid assumptions.
For C >= 1 the finite list always contains a successful candidate. -/
def ceilLog2 (C : ℕ) : ℕ :=
  ((List.range (C+1)).find? (fun j => decide (C ≤ 2^j))).getD C

/-- Natural ceiling of max(q,0), computed from the canonical rational numerator. -/
def nonnegativeCeiling (q : ℚ) : ℕ :=
  (q.num.toNat+q.den-1)/q.den

def dyadic (n : ℕ) : ℚ := 1/(2:ℚ)^n

/-- Lower dyadic root of max(q,0); q >= 0 is the root theorem's guard. -/
def rationalRootLower (q : ℚ) (n : ℕ) : ℚ :=
  (Nat.sqrt ((q.num.toNat*4^n)/q.den):ℚ)/(2:ℚ)^n

def rationalRootUpper (q : ℚ) (n : ℕ) : ℚ :=
  rationalRootLower q n+dyadic n

def cosinePartial (t : ℚ) (N : ℕ) : ℚ :=
  ∑ j in Finset.range (N+1),
    if j%2=0 then (-1:ℚ)^(j/2)*t^j/(Nat.factorial j:ℚ) else 0

def sinePartial (t : ℚ) (N : ℕ) : ℚ :=
  ∑ j in Finset.range (N+1),
    if j%2=1 then (-1:ℚ)^(j/2)*t^j/(Nat.factorial j:ℚ) else 0

def trigDegree (M n : ℕ) : ℕ := 4*M+n+6
def cosineRationalObservation (t : ℚ) (M n : ℕ) : ℚ :=
  cosinePartial t (trigDegree M n)
def sineRationalObservation (t : ℚ) (M n : ℕ) : ℚ :=
  sinePartial t (trigDegree M n)

/-- Here input is one fixed PR rational name in the metatheory. -/
def namedTrigInputPrecision (M n : ℕ) : ℕ := n+ceilLog2 (3^(M+1))+8
def namedTrigDegree (M n : ℕ) : ℕ := 4*(M+1)+n+8

def cosineNamedObservation (input : ℕ → ℚ) (M n : ℕ) : ℚ :=
  cosinePartial (input (namedTrigInputPrecision M n)) (namedTrigDegree M n)
def sineNamedObservation (input : ℕ → ℚ) (M n : ℕ) : ℚ :=
  sinePartial (input (namedTrigInputPrecision M n)) (namedTrigDegree M n)

structure RationalInterval where
  lower : ℚ
  upper : ℚ
  deriving Repr, DecidableEq

def midpoint (interval : RationalInterval) : ℚ :=
  (interval.lower+interval.upper)/2

/-- The vertical variable is stored first; the remaining coordinates are x.
This is an explicit coordinate permutation of the report's F(x,y). -/
def implicitPoint {m : ℕ} (x : Fin m → ℚ) (y : ℚ) : Fin (m+1) → ℚ :=
  Fin.cases y x

def implicitRadius {d : ℕ} (p : PolynomialData d) (M : ℕ) (g : ℚ) : ℚ :=
  min 1 (g/(4*(L p M+1)))

def implicitHorizontalRadius {d : ℕ} (p : PolynomialData d) (M : ℕ) (g : ℚ) : ℚ :=
  g*implicitRadius p M g/(4*(B p M+g+1))

/-- Exact rational test: retain [midpoint,upper] when F(midpoint) <= 0. -/
def bisectStep {m : ℕ} (p : PolynomialData (m+1)) (x : Fin m → ℚ)
    (interval : RationalInterval) : RationalInterval :=
  let q := midpoint interval
  if polyValue p (implicitPoint x q) ≤ 0 then
    ⟨q, interval.upper⟩
  else
    ⟨interval.lower, q⟩

def bisectLoop {m : ℕ} (p : PolynomialData (m+1)) (x : Fin m → ℚ)
    (initial : RationalInterval) : ℕ → RationalInterval
  | 0 => initial
  | k+1 => bisectStep p x (bisectLoop p x initial k)

/-- The theorem requires the stated root, derivative, and box guards. -/
def implicitObservation {m : ℕ} (p : PolynomialData (m+1))
    (x : Fin m → ℚ) (y0 r : ℚ) (n : ℕ) : ℚ :=
  midpoint (bisectLoop p x ⟨y0-r,y0+r⟩ (n+2))

/-- Univariate coefficient lists are in ascending degree order. -/
def univariateValue (coefficients : List ℚ) (t : ℚ) : ℚ :=
  coefficients.foldr (fun a rest => a+t*rest) 0

def derivativeCoefficientsFrom (k : ℕ) : List ℚ → List ℚ
  | [] => []
  | a::rest => (k:ℚ)*a :: derivativeCoefficientsFrom (k+1) rest

def derivativeCoefficients (coefficients : List ℚ) : List ℚ :=
  derivativeCoefficientsFrom 1 coefficients.tail

abbrev PolynomialCurve (d : ℕ) := Fin d → List ℚ

def curveValue {d : ℕ} (curve : PolynomialCurve d) (t : ℚ) : Fin d → ℚ :=
  fun i => univariateValue (curve i) t

def speedBoundFrom (M k : ℕ) : List ℚ → ℚ
  | [] => 0
  | a::rest => |a|*(k:ℚ)*(M:ℚ)^(k-1)+speedBoundFrom M (k+1) rest

def accelerationBoundFrom (M k : ℕ) : List ℚ → ℚ
  | [] => 0
  | a::rest => |a|*(k:ℚ)*((k-1:ℕ):ℚ)*(M:ℚ)^(k-2)+
      accelerationBoundFrom M (k+1) rest

def speedBound {d : ℕ} (curve : PolynomialCurve d) (M : ℕ) : ℚ :=
  ∑ i, speedBoundFrom M 0 (curve i)

def accelerationBound {d : ℕ} (curve : PolynomialCurve d) (M : ℕ) : ℚ :=
  ∑ i, accelerationBoundFrom M 0 (curve i)

def partitionPoint (a b : ℚ) (N j : ℕ) : ℚ :=
  a+(b-a)*(j:ℚ)/(N:ℚ)

def chordSquare {d : ℕ} (curve : PolynomialCurve d) (a b : ℚ) (N j : ℕ) : ℚ :=
  ∑ i, (univariateValue (curve i) (partitionPoint a b N (j+1))-
        univariateValue (curve i) (partitionPoint a b N j))^2

/-- k=n+ell(ceil(2 K (b-a)^2)+1)+3, exactly as in the arc-length proof. -/
def arcMeshExponent {d : ℕ} (curve : PolynomialCurve d) (a b : ℚ)
    (M n : ℕ) : ℕ :=
  let C := nonnegativeCeiling (2*accelerationBound curve M*(b-a)^2)+1
  n+ceilLog2 C+3

/-- Sum of N=2^k lower-root approximations, each at precision n+k+3.
The theorem guard is a<b and M>=max(1,|a|,|b|). -/
def arcLengthObservation {d : ℕ} (curve : PolynomialCurve d) (a b : ℚ)
    (M n : ℕ) : ℚ :=
  let k := arcMeshExponent curve a b M n
  let N := 2^k
  let precision := n+k+3
  ∑ j in Finset.range N, rationalRootLower (chordSquare curve a b N j) precision

end AnalyticGeometryIPRA.AnalyticPrograms
