import AperySpec

/-!
# Finite algebra used by the human proof

STATUS: UNCOMPILED executable definitions and proof-obligation interfaces.
No correctness theorem or completed iPRA derivation is asserted. No axioms
or `sorry` are used. Polynomial lists are in increasing degree order and may
have trailing zero coefficients. All sums, products and arrays are finite.
Every higher-order bounded-loop helper has a fixed body at its uses and is
to be specialized before compilation to first-order PR syntax.
-/

namespace AperyIPRA.FiniteAlgebra

open Spec

abbrev Rat := Fraction
abbrev Poly := List Rat

def rzero : Rat := Fraction.zero
def rone : Rat := Fraction.natural 1
def rnat := Fraction.natural
def radd := Fraction.add
def rneg := Fraction.negate
def rsub := Fraction.subtract
def rmul := Fraction.multiply
def rscale := Fraction.scale

/-- Totalized inversion. Its mathematical use requires a valid nonzero input.
For zero it returns zero; all guarded evaluations below reject that case. -/
def rinverse (a : Rat) : Rat :=
  if a.positive = a.negative then rzero
  else if a.negative ≤ a.positive then
    ⟨a.denominator, 0, a.positive - a.negative⟩
  else ⟨0, a.denominator, a.negative - a.positive⟩

def rdivide (a b : Rat) : Rat := rmul a (rinverse b)

def rpow (a : Rat) : Nat → Rat
  | 0 => rone
  | n + 1 => rmul (rpow a n) a

def reqB (a b : Rat) : Bool :=
  decide (a.positive * b.denominator + b.negative * a.denominator =
    b.positive * a.denominator + a.negative * b.denominator)

def rvalidB (a : Rat) : Bool := decide (0 < a.denominator)

def allNat (test : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allNat test n && test n

def tabulate (f : Nat → Rat) : Nat → List Rat
  | 0 => []
  | n + 1 => tabulate f n ++ [f n]

def pcoeff : Poly → Nat → Rat
  | [], _ => rzero
  | a :: _, 0 => a
  | _ :: p, k + 1 => pcoeff p k

def padd : Poly → Poly → Poly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => radd a b :: padd p q

def pneg (p : Poly) : Poly := p.map rneg
def psub (p q : Poly) : Poly := padd p (pneg q)
def pscale (a : Rat) (p : Poly) : Poly := p.map (rmul a)

def pmul : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => padd (pscale a q) (rzero :: pmul p q)

def ppow (p : Poly) : Nat → Poly
  | 0 => [rone]
  | n + 1 => pmul (ppow p n) p

def pdiffFrom (degree : Nat) : Poly → Poly
  | [] => []
  | a :: p => rscale degree a :: pdiffFrom (degree + 1) p

def pdiff : Poly → Poly
  | [] => []
  | _ :: p => pdiffFrom 1 p

def peval : Poly → Rat → Rat
  | [], _ => rzero
  | a :: p, t => radd a (rmul t (peval p t))

def pcompose : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => padd [a] (pmul q (pcompose p q))

def ptranslate (p : Poly) (a : Rat) : Poly := pcompose p [a, rone]
def pshift (p : Poly) : Poly := ptranslate p rone

/-- Synthetic division: returns q,r with p(t)=(t-a)q(t)+r. Trailing zero
coefficients are retained, so no normalization or unbounded scan is needed. -/
def pdivideLinear : Poly → Rat → Poly × Rat
  | [], _ => ([], rzero)
  | c :: p, a =>
      let qr := pdivideLinear p a
      (qr.2 :: qr.1, radd c (rmul a qr.2))

def pvalidB : Poly → Bool
  | [] => true
  | a :: p => rvalidB a && pvalidB p

/-- The length sum is a sufficient finite coefficient-comparison bound. -/
def peqB (p q : Poly) : Bool :=
  allNat (fun k => reqB (pcoeff p k) (pcoeff q k)) (p.length + q.length)

def pnonzeroB (p : Poly) : Bool := !(peqB p [])

def pdegreeAtMostB (p : Poly) (n : Nat) : Bool :=
  allNat (fun k => if n < k then reqB (pcoeff p k) rzero else true) p.length

def pproduct (f : Nat → Poly) : Nat → Poly
  | 0 => [rone]
  | n + 1 => pmul (pproduct f n) (f n)

def linearPlus (a : Rat) : Poly := [a, rone]
def linearMinus (a : Rat) : Poly := [rneg a, rone]
def pvariable : Poly := [rzero, rone]

/-- A formal polynomial fraction. Denominator validity and nonzeroness are
proof obligations, not silently carried as axioms in this data structure. -/
structure RationalFunction where
  numerator : Poly
  denominator : Poly

abbrev RF := RationalFunction

def rfValidB (f : RF) : Bool :=
  pvalidB f.numerator && pvalidB f.denominator && pnonzeroB f.denominator

def rfOfPoly (p : Poly) : RF := ⟨p, [rone]⟩
def rfConstant (a : Rat) : RF := rfOfPoly [a]
def rfZero : RF := rfOfPoly []
def rfOne : RF := rfConstant rone

def rfAdd (f g : RF) : RF :=
  ⟨padd (pmul f.numerator g.denominator) (pmul g.numerator f.denominator),
   pmul f.denominator g.denominator⟩

def rfNeg (f : RF) : RF := ⟨pneg f.numerator, f.denominator⟩
def rfSub (f g : RF) : RF := rfAdd f (rfNeg g)
def rfMul (f g : RF) : RF :=
  ⟨pmul f.numerator g.numerator, pmul f.denominator g.denominator⟩
def rfScale (a : Rat) (f : RF) : RF :=
  ⟨pscale a f.numerator, f.denominator⟩
def rfPow (f : RF) (k : Nat) : RF :=
  ⟨ppow f.numerator k, ppow f.denominator k⟩

def rfDiff (f : RF) : RF :=
  ⟨psub (pmul (pdiff f.numerator) f.denominator)
      (pmul f.numerator (pdiff f.denominator)),
   ppow f.denominator 2⟩

def rfCompose (f : RF) (p : Poly) : RF :=
  ⟨pcompose f.numerator p, pcompose f.denominator p⟩
def rfShift (f : RF) : RF := rfCompose f [rone, rone]

/-- Formal equality after denominators are cleared. A semantic use also
requires the two denominator polynomials to be nonzero. -/
def rfEqB (f g : RF) : Bool :=
  peqB (pmul f.numerator g.denominator) (pmul g.numerator f.denominator)

/-- Numerical evaluation is guarded: invalid rational inputs/coefficients or
a zero denominator produce none. No numerical evaluation at a pole is used. -/
def rfEval? (f : RF) (t : Rat) : Option Rat :=
  if rvalidB t && pvalidB f.numerator && pvalidB f.denominator then
    let a := peval f.numerator t
    let b := peval f.denominator t
    if b.positive = b.negative then none else some (rdivide a b)
  else none

def rfSum (f : Nat → RF) : Nat → RF
  | 0 => rfZero
  | n + 1 => rfAdd (rfSum f n) (f n)

def Q (n : Nat) : RF :=
  ⟨pproduct (fun j => linearMinus (rnat (j + 1))) n,
   pproduct (fun j => linearPlus (rnat j)) (n + 1)⟩

def R (n : Nat) : RF := rfPow (Q n) 2

/-- Coefficients of 4(2n+1)(-2t^2+t+(2n+1)^2). -/
def s (n : Nat) : Poly :=
  let u := 4 * (2 * n + 1)
  [rnat (u * (2 * n + 1) ^ 2), rnat u, rneg (rnat (2 * u))]

def V (n : Nat) : RF := rfMul (rfOfPoly (s n)) (R n)

def signedDifference (a b : Nat) : Rat := ⟨a, b, 1⟩

def gammaSummand (n k l : Nat) : Rat :=
  if l = k then rzero
  else rdivide (rmul (coefficient n k) (coefficient n l)) (signedDifference l k)

def gamma (n k : Nat) : Rat := Fraction.sum (gammaSummand n k) (n + 1)

def gammaSum (n : Nat) : Rat := Fraction.sum (gamma n) (n + 1)

def bGamma (n : Nat) : Rat :=
  radd (diagonalB n)
    (Fraction.sum (fun k => rmul (gamma n k) (harmonic 2 k)) (n + 1))

/-- Finite arrays encode poles at 0,-1,... by array position. Missing entries
are zero. The polynomial part is constant. -/
structure PartialFractions where
  constantTerm : Rat
  doublePole : List Rat
  simplePole : List Rat

abbrev PF := PartialFractions

def pfValidB (f : PF) : Bool :=
  rvalidB f.constantTerm && pvalidB f.doublePole && pvalidB f.simplePole

def pfAdd (f g : PF) : PF :=
  ⟨radd f.constantTerm g.constantTerm, padd f.doublePole g.doublePole,
    padd f.simplePole g.simplePole⟩
def pfNeg (f : PF) : PF :=
  ⟨rneg f.constantTerm, pneg f.doublePole, pneg f.simplePole⟩
def pfSub (f g : PF) : PF := pfAdd f (pfNeg g)
def pfShift (f : PF) : PF :=
  ⟨f.constantTerm, rzero :: f.doublePole, rzero :: f.simplePole⟩

def poleTerm (coefficient : Rat) (k order : Nat) : RF :=
  ⟨[coefficient], ppow (linearPlus (rnat k)) order⟩

def pfAsRF (f : PF) : RF :=
  rfAdd (rfConstant f.constantTerm)
    (rfAdd
      (rfSum (fun k => poleTerm (pcoeff f.doublePole k) k 2) f.doublePole.length)
      (rfSum (fun k => poleTerm (pcoeff f.simplePole k) k 1) f.simplePole.length))

def qPartial (n : Nat) : PF :=
  ⟨rzero, [], tabulate (coefficient n) (n + 1)⟩

def rPartial (n : Nat) : PF :=
  ⟨rzero, tabulate (fun k => rnat (coeffMagnitude n k ^ 2)) (n + 1),
    tabulate (fun k => rscale 2 (gamma n k)) (n + 1)⟩

/-- The coefficient triple of the formal expression X*x+Y*y+constant. -/
structure FormalTriple where
  x : Rat
  y : Rat
  constantTerm : Rat

def Theta (f : PF) : FormalTriple :=
  let sx := Fraction.sum (fun k => pcoeff f.doublePole k) f.doublePole.length
  let sy := Fraction.sum (fun k => pcoeff f.simplePole k) f.simplePole.length
  let h3 := Fraction.sum (fun k => rmul (pcoeff f.doublePole k) (harmonic 3 k))
    f.doublePole.length
  let h2 := Fraction.sum (fun k => rmul (pcoeff f.simplePole k) (harmonic 2 k))
    f.simplePole.length
  ⟨sx, Fraction.divideByNat sy 2,
    rneg (radd h3 (Fraction.divideByNat h2 2))⟩

def tripleEqv (a b : FormalTriple) : Prop :=
  Fraction.eqv a.x b.x ∧ Fraction.eqv a.y b.y ∧
    Fraction.eqv a.constantTerm b.constantTerm

def thetaShiftDifference (f : PF) : FormalTriple := Theta (pfSub (pfShift f) f)

def pfDerivativeAtOne (f : PF) : Rat :=
  rneg (radd
    (Fraction.sum (fun k => Fraction.divideByNat
      (rscale 2 (pcoeff f.doublePole k)) ((k + 1) ^ 3)) f.doublePole.length)
    (Fraction.sum (fun k => Fraction.divideByNat
      (pcoeff f.simplePole k) ((k + 1) ^ 2)) f.simplePole.length))

def thetaShiftFormula (f : PF) : FormalTriple :=
  ⟨rzero, rzero, Fraction.divideByNat (pfDerivativeAtOne f) 2⟩

/-- s(t)=alpha*t^2+beta*t+delta. The formulas below explicitly divide s by
each pole's linear factor; no partial-fraction algorithm is left opaque. -/
def alpha (n : Nat) : Rat := pcoeff (s n) 2
def beta (n : Nat) : Rat := pcoeff (s n) 1
def sAtNegative (n k : Nat) : Rat := peval (s n) (rneg (rnat k))
def sPrimeAtNegative (n k : Nat) : Rat := peval (pdiff (s n)) (rneg (rnat k))

def vDouble (n k : Nat) : Rat :=
  rmul (rnat (coeffMagnitude n k ^ 2)) (sAtNegative n k)

def vSimple (n k : Nat) : Rat :=
  radd (rmul (rscale 2 (gamma n k)) (sAtNegative n k))
    (rmul (rnat (coeffMagnitude n k ^ 2)) (sPrimeAtNegative n k))

def vConstantSummand (n k : Nat) : Rat :=
  radd (rmul (alpha n) (rnat (coeffMagnitude n k ^ 2)))
    (rmul (rscale 2 (gamma n k)) (rsub (beta n) (rmul (alpha n) (rnat k))))

def vPartial (n : Nat) : PF :=
  ⟨Fraction.sum (vConstantSummand n) (n + 1),
    tabulate (vDouble n) (n + 1), tabulate (vSimple n) (n + 1)⟩

/-- This is zero after the antisymmetry proof for gammaSum. Before that proof
it is retained explicitly, so the reconstruction does not assume cancellation. -/
def vLinearRemainder (n : Nat) : Rat := rmul (alpha n) (rscale 2 (gammaSum n))

def vReconstruction (n : Nat) : RF :=
  rfAdd (pfAsRF (vPartial n)) (rfOfPoly [rzero, vLinearRemainder n])

def certificateLeft (n : Nat) : Poly :=
  let u := linearMinus (rnat n)
  let v := linearPlus (rnat (n + 1))
  padd
    (psub
      (pscale (rnat ((n + 1) ^ 3))
        (pmul (ppow (linearMinus (rnat (n + 1))) 2) (ppow u 2)))
      (pscale (rnat (recurrenceCoefficient n)) (pmul (ppow u 2) (ppow v 2))))
    (pscale (rnat (n ^ 3))
      (pmul (ppow (linearPlus (rnat n)) 2) (ppow v 2)))

def certificateRight (n : Nat) : Poly :=
  psub (pmul (pshift (s n)) (ppow pvariable 4))
    (pmul (s n) (pmul (ppow (linearMinus (rnat n)) 2)
      (ppow (linearPlus (rnat (n + 1))) 2)))

def telescoperLeft (n : Nat) : RF :=
  rfAdd
    (rfSub (rfScale (rnat ((n + 1) ^ 3)) (R (n + 1)))
      (rfScale (rnat (recurrenceCoefficient n)) (R n)))
    (rfScale (rnat (n ^ 3)) (R (n - 1)))

def telescoperRight (n : Nat) : RF := rfSub (rfShift (V n)) (V n)

def delta (power T k : Nat) : Rat :=
  rsub (harmonic power (T + k)) (harmonic power T)

def epsilon (n T : Nat) : Rat :=
  radd
    (Fraction.sum (fun k => rscale (coeffMagnitude n k ^ 2) (delta 3 T k)) (n + 1))
    (Fraction.sum (fun k => rmul (gamma n k) (delta 2 T k)) (n + 1))

def E (n : Nat) : Nat := (n + 1) ^ 3 * 64 ^ n
def auxiliaryM (n K : Nat) : Nat := n + 1 + 6 * K
def auxiliaryT (n M K : Nat) : Nat :=
  let m := auxiliaryM n K
  M + m + 2 * K * (E m + 1)
def squeezeChoice (x y : Rat) : Nat := 2 * x.denominator * y.denominator

/-- The derivative written directly from the finite partial fractions,
evaluated at u+1. Every displayed denominator is strictly positive. -/
def rPrimeAtSucc (n u : Nat) : Rat :=
  rneg (rscale 2
    (radd
      (Fraction.sum (fun k => Fraction.divideByNat
        (rnat (coeffMagnitude n k ^ 2)) ((u + 1 + k) ^ 3)) (n + 1))
      (Fraction.sum (fun k => Fraction.divideByNat
        (gamma n k) ((u + 1 + k) ^ 2)) (n + 1))))

/-- F(n,T)=-1/2 sum_{1<=t<=T}R'_n(t), using the explicit PF expression.
The equality to formal rational-function differentiation remains to be proved. -/
def finiteDerivativeSum (n T : Nat) : Rat :=
  rneg (Fraction.divideByNat (Fraction.sum (rPrimeAtSucc n) T) 2)

def optionAdd : Option Rat → Option Rat → Option Rat
  | some a, some b => some (radd a b)
  | _, _ => none

/-- Independent guarded evaluation of the formal quotient-rule derivative. -/
def derivativeSum? (n : Nat) : Nat → Option Rat
  | 0 => some rzero
  | T + 1 => optionAdd (derivativeSum? n T) (rfEval? (rfDiff (R n)) (rnat (T + 1)))

def formalDerivativeSum? (n T : Nat) : Option Rat :=
  match derivativeSum? n T with
  | none => none
  | some v => some (rneg (Fraction.divideByNat v 2))

def optionEqv (a : Option Rat) (b : Rat) : Prop :=
  match a with
  | none => False
  | some a => Fraction.eqv a b

def finitePFRight (n T : Nat) : Rat := radd (finiteLinearForm n T) (epsilon n T)
def ratio (n : Nat) : Rat := Fraction.divideByNat (B n) (A n)
def ratioDifference (n m : Nat) : Rat := rsub (ratio m) (ratio n)
def wronskian (n : Nat) : Rat :=
  rsub (rscale (A n) (B (n + 1))) (rscale (A (n + 1)) (B n))
def ratioIncrement (n : Nat) : Rat :=
  ⟨6, 0, (n + 1) ^ 3 * A n * A (n + 1)⟩
def finiteRatioTail (n m : Nat) : Rat :=
  Fraction.sum (fun j => ratioIncrement (n + j)) (m - n)
def geometricSum (J : Nat) : Rat :=
  Fraction.sum (fun j => Fraction.reciprocal (32 ^ (2 * j + 1))) J
def geometricMajorant : Rat := ⟨32, 0, 1023⟩

/-- Concrete bounded definitions for the sparse denominator argument. -/
def multinomialDenominator (m : Nat) : Nat :=
  factorial (21 * m) * factorial (14 * m) * factorial (6 * m) * factorial m
def multinomial (m : Nat) : Nat :=
  divide (factorial (42 * m)) (multinomialDenominator m)
def multinomialMajorantBase : Rat :=
  ⟨42 ^ 42, 0, 21 ^ 21 * 14 ^ 14 * 6 ^ 6⟩
def sparseConstantComparison : Prop :=
  (42 ^ 42) ^ 3 ≤ 28 ^ 41 * (21 ^ 21 * 14 ^ 14 * 6 ^ 6) ^ 3
def floorSum (t : Nat) : Nat :=
  divide t 2 + divide t 3 + divide t 7 + divide t 42
def floorDefect (t : Nat) : Nat := t - floorSum t
def isPrimeB (p : Nat) : Bool :=
  decide (2 ≤ p) && allNat
    (fun d => if 2 ≤ d then !(dividesB d p) else true) p
def valuation (p a : Nat) : Nat :=
  if 2 ≤ p then
    if a = 0 then 0 else
      sumNat (fun j => if dividesB (p ^ (j + 1)) a then 1 else 0) a
  else 0
def factorialValuation (p n : Nat) : Nat :=
  if 2 ≤ p then sumNat (fun j => divide n (p ^ (j + 1))) n else 0

/-!
These are explicit proof targets, NOT assumed lemmas. In particular the
polynomial identity is valid at the level of coefficient lists, while the
formal derivative evaluation is allowed only through the nonzero guard.
Internal versions of the targets and their QF induction invariants remain
to be constructed; no inhabitant of this record is supplied.
-/
structure AlgebraProofObligations : Prop where
  divisionByLinear : ∀ p a, pvalidB p = true → rvalidB a = true →
    let qr := pdivideLinear p a
    peqB p (padd (pmul (linearMinus a) qr.1) [qr.2]) = true
  rationalFunctionValidity : ∀ n,
    rfValidB (Q n) = true ∧ rfValidB (R n) = true ∧ rfValidB (V n) = true
  qPartialFractions : ∀ n, rfEqB (Q n) (pfAsRF (qPartial n)) = true
  rPartialFractions : ∀ n, rfEqB (R n) (pfAsRF (rPartial n)) = true
  gammaCancels : ∀ n, Fraction.eqv (gammaSum n) rzero
  bGammaIdentity : ∀ n, Fraction.eqv (B n) (bGamma n)
  polynomialCertificate : ∀ n, peqB (certificateLeft n) (certificateRight n) = true
  vPartialFractions : ∀ n, rfEqB (V n) (vReconstruction n) = true
  vLinearVanishes : ∀ n, Fraction.eqv (vLinearRemainder n) rzero
  telescoper : ∀ n, 1 ≤ n → rfEqB (telescoperLeft n) (telescoperRight n) = true
  thetaR : ∀ n, tripleEqv (Theta (rPartial n)) ⟨rnat (A n), rzero, rneg (B n)⟩
  thetaShift : ∀ f, pfValidB f = true →
    tripleEqv (thetaShiftDifference f) (thetaShiftFormula f)
  vDerivativeVanishes : ∀ n, 1 ≤ n → optionEqv (rfEval? (rfDiff (V n)) rone) rzero
  derivativeAgreement : ∀ n u,
    optionEqv (rfEval? (rfDiff (R n)) (rnat (u + 1))) (rPrimeAtSucc n u)
  finiteDerivativeAgreement : ∀ n T,
    optionEqv (formalDerivativeSum? n T) (finiteDerivativeSum n T)
  finitePartialFractions : ∀ n T,
    Fraction.eqv (finiteDerivativeSum n T) (finitePFRight n T)
  finiteRatioTelescoping : ∀ n m, n ≤ m →
    Fraction.eqv (ratioDifference n m) (finiteRatioTail n m)
  geometricBound : ∀ J, Fraction.le (geometricSum J) geometricMajorant

end AperyIPRA.FiniteAlgebra
