/-!
# Exact finite arithmetic specification for Apéry's theorem in iPRA

STATUS: executable specification and formalization outline, UNCOMPILED in
the authoring environment. No completed Lean proof is claimed. This file
contains neither axioms nor `sorry`. Its final obligation structure has no
supplied inhabitant. No real numbers or infinite sums occur.

All quotients below are explicitly bounded primitive-recursive searches.
`sumNat` and `Fraction.sum` are specification helpers: each occurrence has a
fixed summand and must be specialized before compilation to first-order PR
syntax. The astronomical witness is mathematically explicit, not practical.
-/

namespace AperyIPRA.Spec

/-- Bounded sum of a fixed summand, with endpoint excluded. -/
def sumNat (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumNat f n + f n

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Scan candidate quotients 1,...,k. Recursion is bounded by the numerator. -/
def quotientScan (a d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      if (k + 1) * d ≤ a then k + 1 else quotientScan a d k

/-- Totalized natural division; the zero-divisor convention is zero. -/
def divide (a d : Nat) : Nat :=
  if d = 0 then 0 else quotientScan a d a

def remainder (a d : Nat) : Nat := a - d * divide a d

def dividesB (d a : Nat) : Bool :=
  if d = 0 then decide (a = 0) else decide (remainder a d = 0)

/-- Scan positive common multiples, retaining the first successful candidate. -/
def lcmScan (a b : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
      let previous := lcmScan a b k
      if previous = 0 then
        if dividesB a (k + 1) && dividesB b (k + 1) then k + 1 else 0
      else previous

/-- At positive inputs a*b is a common multiple, hence is a search bound. -/
def lcm (a b : Nat) : Nat :=
  if a = 0 then 0 else if b = 0 then 0 else lcmScan a b (a * b)

def D : Nat → Nat
  | 0 => 1
  | n + 1 => lcm (D n) (n + 1)

def choose (n k : Nat) : Nat :=
  if k ≤ n then divide (factorial n) (factorial k * factorial (n - k)) else 0

def evenB (n : Nat) : Bool := decide (remainder n 2 = 0)

/-- Raw fraction denoting (positive-negative)/denominator. -/
structure Fraction where
  positive : Nat
  negative : Nat
  denominator : Nat
  deriving Repr, DecidableEq

namespace Fraction

def zero : Fraction := ⟨0, 0, 1⟩
def natural (a : Nat) : Fraction := ⟨a, 0, 1⟩
def reciprocal (d : Nat) : Fraction := ⟨1, 0, d⟩
def negate (a : Fraction) : Fraction := ⟨a.negative, a.positive, a.denominator⟩

def add (a b : Fraction) : Fraction :=
  ⟨a.positive * b.denominator + b.positive * a.denominator,
   a.negative * b.denominator + b.negative * a.denominator,
   a.denominator * b.denominator⟩

def subtract (a b : Fraction) : Fraction := add a (negate b)

def multiply (a b : Fraction) : Fraction :=
  ⟨a.positive * b.positive + a.negative * b.negative,
   a.positive * b.negative + a.negative * b.positive,
   a.denominator * b.denominator⟩

def scale (c : Nat) (a : Fraction) : Fraction :=
  ⟨c * a.positive, c * a.negative, a.denominator⟩

/-- This operation is division only when d>0, proved separately. -/
def divideByNat (a : Fraction) (d : Nat) : Fraction :=
  ⟨a.positive, a.negative, a.denominator * d⟩

def alternating (j : Nat) (a : Fraction) : Fraction :=
  if evenB j then a else negate a

def valid (a : Fraction) : Prop := 0 < a.denominator

def eqv (a b : Fraction) : Prop :=
  a.positive * b.denominator + b.negative * a.denominator =
    b.positive * a.denominator + a.negative * b.denominator

def le (a b : Fraction) : Prop :=
  a.positive * b.denominator + b.negative * a.denominator ≤
    b.positive * a.denominator + a.negative * b.denominator

def lt (a b : Fraction) : Prop :=
  a.positive * b.denominator + b.negative * a.denominator <
    b.positive * a.denominator + a.negative * b.denominator

def ltB (a b : Fraction) : Bool :=
  decide (a.positive * b.denominator + b.negative * a.denominator <
    b.positive * a.denominator + a.negative * b.denominator)

def sum (f : Nat → Fraction) : Nat → Fraction
  | 0 => zero
  | n + 1 => add (sum f n) (f n)

end Fraction

open Fraction

/-- H_s(k) = sum_{1 <= j <= k} j^(-s), as a raw rational. -/
def harmonic (s : Nat) : Nat → Fraction
  | 0 => zero
  | k + 1 => add (harmonic s k) (reciprocal ((k + 1) ^ s))

def coeffMagnitude (n k : Nat) : Nat := choose n k * choose (n + k) k

/-- c(n,k) = (-1)^(n-k) choose(n,k) choose(n+k,k), for k<=n. -/
def coefficient (n k : Nat) : Fraction :=
  alternating (n - k) (natural (coeffMagnitude n k))

def A (n : Nat) : Nat :=
  sumNat (fun k => coeffMagnitude n k ^ 2) (n + 1)

def diagonalB (n : Nat) : Fraction :=
  sum (fun k => scale (coeffMagnitude n k ^ 2) (harmonic 3 k)) (n + 1)

def crossB (n k l : Nat) : Fraction :=
  if k < l then
    multiply
      (divideByNat (multiply (coefficient n k) (coefficient n l)) (l - k))
      (subtract (harmonic 2 k) (harmonic 2 l))
  else zero

def B (n : Nat) : Fraction :=
  add (diagonalB n)
    (sum (fun k => sum (fun l => crossB n k l) (n + 1)) (n + 1))

/-- Signed integer coefficients for D(n)^3 B(n), once integrality is proved.
Cancel the positive/negative numerator before division: the separate raw
numerators need not individually be divisible by the raw denominator. -/
def scaledBPositive (n : Nat) : Nat :=
  let b := B n
  divide (D n ^ 3 * (b.positive - b.negative)) b.denominator

def scaledBNegative (n : Nat) : Nat :=
  let b := B n
  divide (D n ^ 3 * (b.negative - b.positive)) b.denominator

def scaledBInteger (n : Nat) : Fraction :=
  ⟨scaledBPositive n, scaledBNegative n, 1⟩

/-- h_n = (n+1)^3 A(n+1). -/
def h (n : Nat) : Nat := (n + 1) ^ 3 * A (n + 1)

/-- n(q), with q the ACTUAL positive denominator. -/
def aperyIndex (q : Nat) : Nat := 42 ^ (q + 1)

def cutoff (q : Nat) : Nat := A (aperyIndex q) * h (aperyIndex q)

def rationalCandidate (pPositive pNegative q : Nat) : Fraction :=
  ⟨pPositive, pNegative, q⟩

def partialZeta (M : Nat) : Fraction := harmonic 3 M
def zetaTail (M : Nat) : Fraction := reciprocal (2 * M ^ 2)
def separationMargin (q : Nat) : Fraction := reciprocal (cutoff q)

def leftEndpoint (q : Nat) : Fraction := partialZeta (cutoff q)
def rightEndpoint (q : Nat) : Fraction :=
  add (partialZeta (cutoff q)) (zetaTail (cutoff q))

/-- Quantitative rational separation from the finite interval containing ζ(3). -/
def Separated (pPositive pNegative q : Nat) : Prop :=
  lt (add (rationalCandidate pPositive pNegative q) (separationMargin q))
    (leftEndpoint q) ∨
  lt (add (rightEndpoint q) (separationMargin q))
    (rationalCandidate pPositive pNegative q)

/-- q0 is shifted once, so the final checker has no zero-denominator branch. -/
def separationTest (pPositive pNegative q0 : Nat) : Bool :=
  let q := q0 + 1
  ltB (add (rationalCandidate pPositive pNegative q) (separationMargin q))
      (leftEndpoint q) ||
    ltB (add (rightEndpoint q) (separationMargin q))
      (rationalCandidate pPositive pNegative q)

/-- This fixed total natural-number program is the object-theory compiler target. -/
def checkApery (pPositive pNegative q0 : Nat) : Nat :=
  if separationTest pPositive pNegative q0 then 0 else 1

def AperyStatement : Prop :=
  ∀ pPositive pNegative q0 : Nat, Separated pPositive pNegative (q0 + 1)

def CheckerStatement : Prop :=
  ∀ pPositive pNegative q0 : Nat, checkApery pPositive pNegative q0 = 0

def finiteLinearForm (n M : Nat) : Fraction :=
  subtract (scale (A n) (partialZeta M)) (B n)

def finiteLowerBound (n M : Nat) : Fraction :=
  subtract (scale 6 (reciprocal (h n)))
    (divideByNat (natural (A n)) (2 * M ^ 2))

def recurrenceCoefficient (n : Nat) : Nat :=
  (2 * n + 1) * (17 * n ^ 2 + 17 * n + 5)

/-- J = D(n)^3 (A(n) p - q B(n)), represented as J+ - J-. -/
def integerFormPositive (n pPositive q : Nat) : Nat :=
  D n ^ 3 * A n * pPositive + q * scaledBNegative n

def integerFormNegative (n pNegative q : Nat) : Nat :=
  D n ^ 3 * A n * pNegative + q * scaledBPositive n

/-!
Named EXTERNAL proof obligations. No inhabitant is supplied. Even an external
inhabitant of this record would not itself be an object-language iPRA proof;
the internal counterparts must be proved with `PRA.qfInd` and the constructors
of `Prf`. This record is a work list, not an extension of the axiom system.
-/
structure FiniteProofObligations : Prop where
  aperyPositive : ∀ n, 0 < A n
  heightDominates : ∀ n, A n ≤ h n
  denominatorPositive : ∀ n, 0 < D n
  rationalValidity : ∀ n, valid (B n)
  harmonicValidity : ∀ s n, valid (harmonic s n)
  integrality : ∀ n, eqv (scale (D n ^ 3) (B n)) (scaledBInteger n)
  recurrenceA : ∀ k,
    (k + 2) ^ 3 * A (k + 2) + (k + 1) ^ 3 * A k =
      recurrenceCoefficient (k + 1) * A (k + 1)
  recurrenceB : ∀ k,
    eqv (add (scale ((k + 2) ^ 3) (B (k + 2)))
      (scale ((k + 1) ^ 3) (B k)))
      (scale (recurrenceCoefficient (k + 1)) (B (k + 1)))
  casoratian : ∀ n,
    eqv (scale ((n + 1) ^ 3)
      (subtract (scale (A n) (B (n + 1))) (scale (A (n + 1)) (B n))))
      (natural 6)
  aperyGrowth : ∀ n, 48 ≤ n → 32 ^ n ≤ 32 ^ 48 * A n
  sparseLCMBound : ∀ k, D (42 ^ k) ^ 3 ≤ 28 ^ (42 ^ k)
  finiteBounds : ∀ n M, 48 ≤ n → 1 ≤ M →
    le (finiteLowerBound n M) (finiteLinearForm n M) ∧
    le (finiteLinearForm n M) (reciprocal (A n))
  tailBound : ∀ M K, 1 ≤ M → M ≤ K →
    le zero (subtract (partialZeta K) (partialZeta M)) ∧
    le (subtract (partialZeta K) (partialZeta M)) (zetaTail M)
  witnessBudget : ∀ q, 1 ≤ q →
    8 * q * D (aperyIndex q) ^ 3 < A (aperyIndex q)
  cutoffPositive : ∀ q, 0 < cutoff q
  indexLarge : ∀ q, 1 ≤ q → 48 ≤ aperyIndex q

end AperyIPRA.Spec
