/-!
# Executable arithmetic specification of the Basel statement

STATUS: outline/specification, not a completed formal proof; not compiled in
the authoring environment.  This file contains no `sorry` and no axioms.

Everything below uses natural numbers and explicitly terminating recursion.
`Fraction` is a raw triple (positive numerator, negative numerator,
denominator).  It denotes (positive - negative) / denominator, but no real
numbers, rational quotients, infinite sequences, or limits occur in the code.

The higher-order helper `sum` is specification notation only.  Every use has
a fixed body; the object-theory compiler must compile each such use to a
first-order primitive recursive definition.  Merely defining these Lean
functions does not prove their representability or their correctness in iPRA.
-/

namespace BaselIPRA.Spec

structure Fraction where
  positive : Nat
  negative : Nat
  denominator : Nat
  deriving Repr, DecidableEq

namespace Fraction

def zero : Fraction := ⟨0, 0, 1⟩

def natural (n : Nat) : Fraction := ⟨n, 0, 1⟩

def reciprocal (d : Nat) : Fraction := ⟨1, 0, d⟩

def negate (a : Fraction) : Fraction :=
  ⟨a.negative, a.positive, a.denominator⟩

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

/-- Callers must separately establish `0 < d` before using this as division. -/
def divideByNat (a : Fraction) (d : Nat) : Fraction :=
  ⟨a.positive, a.negative, a.denominator * d⟩

def alternating (j : Nat) (a : Fraction) : Fraction :=
  if j % 2 = 0 then a else negate a

def valid (a : Fraction) : Prop := 0 < a.denominator

/-- Cross-multiplied equality; it has the intended meaning at valid inputs. -/
def eqv (a b : Fraction) : Prop :=
  a.positive * b.denominator + b.negative * a.denominator =
    b.positive * a.denominator + a.negative * b.denominator

/-- Cross-multiplied order; it has the intended meaning at valid inputs. -/
def le (a b : Fraction) : Prop :=
  a.positive * b.denominator + b.negative * a.denominator ≤
    b.positive * a.denominator + a.negative * b.denominator

def absLe (a bound : Fraction) : Prop :=
  le a bound ∧ le (negate a) bound

/-- The exact QF matrix expressing `|a| ≤ 2^(-k)`. -/
def absLePowTwo (a : Fraction) (k : Nat) : Prop :=
  a.positive * 2 ^ k ≤ a.negative * 2 ^ k + a.denominator ∧
  a.negative * 2 ^ k ≤ a.positive * 2 ^ k + a.denominator

instance (a : Fraction) (k : Nat) : Decidable (absLePowTwo a k) :=
  inferInstanceAs (Decidable
    (a.positive * 2 ^ k ≤ a.negative * 2 ^ k + a.denominator ∧
     a.negative * 2 ^ k ≤ a.positive * 2 ^ k + a.denominator))

def sum (f : Nat → Fraction) : Nat → Fraction
  | 0 => zero
  | n + 1 => add (sum f n) (f n)

end Fraction

open Fraction

/-- A_N = sum_{j<N} (-1)^j/(2j+1). -/
def A : Nat → Fraction
  | 0 => zero
  | n + 1 => add (A n) (alternating n (reciprocal (2 * n + 1)))

/-- H_N = sum_{j<N} 1/(2j+1). -/
def H : Nat → Fraction
  | 0 => zero
  | n + 1 => add (H n) (reciprocal (2 * n + 1))

/-- O_N = sum_{j<N} 1/(2j+1)^2. -/
def O : Nat → Fraction
  | 0 => zero
  | n + 1 => add (O n) (reciprocal ((2 * n + 1) ^ 2))

/-- S_N = sum_{j=1}^N 1/j^2. -/
def S : Nat → Fraction
  | 0 => zero
  | n + 1 => add (S n) (reciprocal ((n + 1) ^ 2))

/-- The sum is empty at N=0 or N=1. -/
def T (N : Nat) : Fraction :=
  sum (fun j => alternating j (divideByNat (H (j + 1)) (j + 1))) (N - 1)

/-- The error in grouping A_N^2 by the index difference. -/
def E (N : Nat) : Fraction :=
  sum (fun j => alternating j
    (divideByNat (subtract (H N) (H (N - (j + 1)))) (j + 1))) (N - 1)

/-- D_N = A_N^2 - T_N. -/
def D (N : Nat) : Fraction := subtract (multiply (A N) (A N)) (T N)

/-- Terms with i+j < N-1, the triangular part of the square. -/
def triangle (N : Nat) : Fraction :=
  sum (fun i => sum (fun j =>
    if i + j + 1 < N then
      alternating (i + j) (reciprocal ((2 * i + 1) * (2 * j + 1)))
    else zero) N) N

/-- Error whose smallness is the arithmetic form of the Basel identity. -/
def residualAt (N n : Nat) : Fraction :=
  subtract (scale 6 (S n))
    (multiply (scale 4 (A N)) (scale 4 (A N)))

def exponent (k : Nat) : Nat := 2 * k + 7

def cutoff (k : Nat) : Nat := 2 ^ exponent k

def piApprox (k : Nat) : Fraction := scale 4 (A (cutoff k))

def residual (k n : Nat) : Fraction := residualAt (cutoff k) n

/-- An equivalent raw-fraction form useful for the finite intermediate lemmas. -/
def FractionBaselStatement : Prop :=
  ∀ k n : Nat, cutoff k ≤ n → absLePowTwo (residual k n) k

def checkFractionBasel (k n : Nat) : Nat :=
  if cutoff k ≤ n then
    if absLePowTwo (residual k n) k then 0 else 1
  else 0

/-- Specification helper; specialize its fixed bodies before PR compilation. -/
def sumNat (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumNat f n + f n

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- A common denominator containing every denominator used when n >= N(k). -/
def commonDenominator (n : Nat) : Nat := factorial (2 * n)

/-- Pairing the positive and negative terms makes every summand nonnegative.
Natural subtraction is exact here under the guard n >= N(k). -/
def commonOddNumerator (k n : Nat) : Nat :=
  let d := commonDenominator n
  sumNat (fun j => d / (4 * j + 1) - d / (4 * j + 3)) (cutoff k / 2)

def commonBaselNumerator (n : Nat) : Nat :=
  let d := commonDenominator n
  sumNat (fun j => (d / (j + 1)) ^ 2) n

/-- Absolute difference, using only natural truncated subtraction. -/
def delta (a b : Nat) : Nat := (a - b) + (b - a)

def integerBound (k n : Nat) : Prop :=
  2 ^ k * delta (6 * commonBaselNumerator n)
    (16 * commonOddNumerator k n ^ 2) ≤ commonDenominator n ^ 2

instance (k n : Nat) : Decidable (integerBound k n) :=
  inferInstanceAs (Decidable
    (2 ^ k * delta (6 * commonBaselNumerator n)
      (16 * commonOddNumerator k n ^ 2) ≤ commonDenominator n ^ 2))

/-- Recommended final first-order target: a universal natural-number inequality. -/
def BaselStatement : Prop :=
  ∀ k n : Nat, cutoff k ≤ n → integerBound k n

/-- Final compiler target: all arithmetic is on natural numbers. -/
def checkBasel (k n : Nat) : Nat :=
  if cutoff k ≤ n then
    if integerBound k n then 0 else 1
  else 0

/-!
The following structure records named, as-yet-unformalized arithmetic proof
obligations.  No inhabitant is supplied.  In particular this is neither an
axiomatization accepted as true nor a proof of BaselStatement.
-/
structure FiniteProofObligations : Prop where
  denominators : ∀ n, valid (A n) ∧ valid (H n) ∧ valid (O n) ∧ valid (S n)
  triangleIdentity : ∀ N, 1 ≤ N → eqv (triangle N) (T N)
  differenceIdentity : ∀ N, 1 ≤ N →
    eqv (multiply (A N) (A N)) (add (subtract (O N) (T N)) (E N))
  triangleError : ∀ N, 1 ≤ N → absLe (D N) (divideByNat (H N) N)
  differenceError : ∀ N, 1 ≤ N → absLe (E N) (divideByNat (H N) N)
  oddEvenIdentity : ∀ N,
    eqv (scale 4 (O N)) (subtract (scale 4 (S (2 * N))) (S N))
  doubledTailLower : ∀ N, 1 ≤ N →
    le (reciprocal (4 * N)) (subtract (S (2 * N)) (S N))
  doubledTailUpper : ∀ N, 1 ≤ N →
    le (subtract (S (2 * N)) (S N)) (reciprocal (2 * N))
  ordinaryTail : ∀ N n, 1 ≤ N → N ≤ n →
    le zero (subtract (S n) (S N)) ∧
      le (subtract (S n) (S N)) (reciprocal N)
  harmonicDyadic : ∀ r,
    le (H (2 ^ r)) (divideByNat (natural (r + 2)) 2)
  uniformDyadic : ∀ r n, 2 ^ r ≤ n →
    absLe (residualAt (2 ^ r) n)
      (divideByNat (natural (8 * r + 20)) (2 ^ r))
  precisionBudget : ∀ k, 16 * k + 76 ≤ 128 * 2 ^ k
  commonDenominatorPositive : ∀ n, 0 < commonDenominator n
  commonOddRepresentation : ∀ k n, cutoff k ≤ n →
    eqv (A (cutoff k))
      ⟨commonOddNumerator k n, 0, commonDenominator n⟩
  commonBaselRepresentation : ∀ n,
    eqv (S n) ⟨commonBaselNumerator n, 0, commonDenominator n ^ 2⟩

end BaselIPRA.Spec
