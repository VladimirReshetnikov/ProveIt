/-!
# Finite Gaussian infrastructure — design blueprint

STATUS: uncompiled blueprint.  This file is not a claim of a completed Lean
formalization.  It contains no placeholder proof of a headline theorem.

The intended first milestone is to turn the exact finite algebra below into a
small checked library and then compile each Boolean verifier into a `PR k`
symbol with defining equations in `PRAAx`.
-/

import Std

namespace NormalDistributionIPRA

/-- A signed rational presentation; normalization is not required for checking. -/
structure SRat where
  num : Int
  den : Nat
  denPos : 0 < den

/-- Closed rational interval.  A production version also carries `lo ≤ hi`. -/
structure RatInterval where
  lo : SRat
  hi : SRat

/-- Exact finite certificate interface: data plus a decidable checker. -/
structure Certificate (Input Output : Type) where
  produce : Input → Output
  check : Input → Output → Bool

/-- Primitive recursion defining `(2m-1)!!`, with `(-1)!! = 1` encoded at `m=0`. -/
def oddDoubleFactorial : Nat → Nat
  | 0 => 1
  | m + 1 => (2 * m + 1) * oddDoubleFactorial m

/-- Standard-normal moments: `E[Z^n]`, represented as integers. -/
def stdMoment : Nat → Int
  | 0 => 1
  | 1 => 0
  | n + 2 => Int.ofNat (n + 1) * stdMoment n

/-- Coefficient lists are in increasing degree order. -/
abbrev ZPoly := List Int

private def coeff (p : ZPoly) (k : Nat) : Int := p.getD k 0

private def trimLength (p q : ZPoly) : Nat := Nat.max p.length q.length

/-- Coefficientwise addition. -/
def polyAdd (p q : ZPoly) : ZPoly :=
  List.ofFn fun i : Fin (trimLength p q) => coeff p i * 1 + coeff q i

/-- Coefficientwise subtraction. -/
def polySub (p q : ZPoly) : ZPoly :=
  List.ofFn fun i : Fin (trimLength p q) => coeff p i - coeff q i

/-- Multiply a polynomial by an integer. -/
def polyScale (a : Int) (p : ZPoly) : ZPoly := p.map (a * ·)

/-- Multiply by the indeterminate. -/
def polyX (p : ZPoly) : ZPoly := 0 :: p

/-- Probabilists' Hermite polynomials, `He_{n+1}=x He_n-n He_{n-1}`. -/
def hermite : Nat → ZPoly
  | 0 => [1]
  | 1 => [0, 1]
  | n + 2 => polySub (polyX (hermite (n + 1)))
      (polyScale (Int.ofNat (n + 1)) (hermite n))

/-- A finite moment-recurrence checker.  This is the Boolean graph that should
later be reflected into object-language equations and proved by `PRA.qfInd`. -/
def checkMomentPrefix (N : Nat) : Bool :=
  (List.range N).all fun n =>
    if n = 0 then stdMoment 0 = 1
    else if n = 1 then stdMoment 1 = 0
    else stdMoment n = Int.ofNat (n - 1) * stdMoment (n - 2)

/-- Intended certificate record for an enclosure of `exp(-q)`.
The production checker uses an alternating finite Taylor sum after range
reduction and verifies all inequalities by cross multiplication. -/
structure ExpNegCert where
  inputNum : Nat
  inputDen : Nat
  rangePower : Nat
  terms : Nat
  enclosure : RatInterval

/-- Intended certificate record for a CDF enclosure.
`seriesTerms` is chosen past the decreasing-term threshold; the checker verifies
an alternating remainder bound and combines it with a certified enclosure of
`1/sqrt(2*pi)`. -/
structure CDFCert where
  x : SRat
  precision : Nat
  seriesTerms : Nat
  enclosure : RatInterval

/-- Intended certificate record for a Mills-ratio enclosure. -/
structure MillsCert where
  x : SRat
  depth : Nat
  density : RatInterval
  tail : RatInterval

/-- Intended certificate record for an interval-valued quantile. -/
structure QuantileCert where
  probability : SRat
  precision : Nat
  bracket : RatInterval
  cdfAtLo : RatInterval
  cdfAtHi : RatInterval

/-- The object-language work should prove soundness of these checkers, not merely
execute them in Lean's metatheory. -/
structure GaussianFiniteAPI where
  expNeg : Certificate ExpNegCert RatInterval
  cdf : Certificate CDFCert RatInterval
  mills : Certificate MillsCert RatInterval
  quantile : Certificate QuantileCert RatInterval

end NormalDistributionIPRA
