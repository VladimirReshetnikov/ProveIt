import BellCore

/-!
Executable arithmetic specifications for the remaining work.

Definitions ending in `Target` are propositions to be proved, NOT axioms or
theorems. All approximants are finite rational calculations. The correctness
of their error bounds is established in the accompanying human proof and
remains a formalization task. Quantification over a function in this file is
metatheoretic; the final iPRA instances use fixed PR program codes.
-/

namespace BellIPRA

/-- Unreduced rational code; denominator zero is an invalid code. -/
structure QCode where
  num : Int
  den : Nat
  deriving Repr, DecidableEq

namespace QCode

def valid (x : QCode) : Prop := 0 < x.den
def ofNat (n : Nat) : QCode := ⟨Int.ofNat n, 1⟩
def zero : QCode := ofNat 0
def one : QCode := ofNat 1
def add (x y : QCode) : QCode :=
  ⟨x.num * Int.ofNat y.den + y.num * Int.ofNat x.den, x.den * y.den⟩
def neg (x : QCode) : QCode := ⟨-x.num, x.den⟩
def sub (x y : QCode) : QCode := add x (neg y)
def mul (x y : QCode) : QCode := ⟨x.num * y.num, x.den * y.den⟩
def inv (x : QCode) : QCode :=
  ⟨if x.num < 0 then -Int.ofNat x.den else Int.ofNat x.den, x.num.natAbs⟩
def div (x y : QCode) : QCode := mul x (inv y)
def abs (x : QCode) : QCode := ⟨Int.ofNat x.num.natAbs, x.den⟩
def le (x y : QCode) : Prop :=
  x.num * Int.ofNat y.den ≤ y.num * Int.ofNat x.den
instance (x y : QCode) : Decidable (le x y) := inferInstanceAs (Decidable (_ ≤ _))
def pow (x : QCode) : Nat → QCode
  | 0 => one
  | n + 1 => mul (pow x n) x
def sum (f : Nat → QCode) : Nat → QCode
  | 0 => zero
  | n + 1 => add (sum f n) (f n)
def eps (t : Nat) : QCode := ⟨1, 2 ^ t⟩

end QCode

open QCode

/-- Truncated exponential, with a deliberately generous PR truncation. -/
def expApprox (x : QCode) (t : Nat) : QCode :=
  let m := x.num.natAbs + 1
  let K := 8 * (m + 1) ^ 2 + 2 * t + 16
  QCode.sum (fun j => QCode.div (QCode.pow x j) (QCode.ofNat (factorial j))) K

/-- Atanh-series logarithm. The logarithm of a nonpositive or invalid code
    is set to zero to keep this a total arithmetic program. -/
def logApprox (x : QCode) (t : Nat) : QCode :=
  if x.num ≤ 0 ∨ x.den = 0 then QCode.zero else
  let u := x.num.natAbs
  let v := x.den
  let z : QCode := ⟨Int.ofNat u - Int.ofNat v, u + v⟩
  let N := (u + v) ^ 2 * 2 ^ (t + 4)
  QCode.mul (QCode.ofNat 2)
    (QCode.sum (fun j => QCode.div (QCode.pow z (2 * j + 1))
      (QCode.ofNat (2 * j + 1))) N)

/-- First successful index below the given bound; the bound itself is the
    default when every test fails. This is bounded search, not minimization. -/
def boundedMin (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | N + 1 =>
    let j := boundedMin p N
    if j < N then j else if p N then N else N + 1

/-- An upper dyadic approximation to W(n), using only comparisons of
    rational truncated exponential sums. The paper proves a PR error bound. -/
def wApprox (n t : Nat) : QCode :=
  let M := 2 ^ (t + 2)
  let point (k : Nat) : QCode := ⟨Int.ofNat k, M⟩
  let p (k : Nat) : Bool :=
    decide (QCode.le (QCode.ofNat n)
      (QCode.mul (point k) (expApprox (point k) (t + n + 8))))
  point (boundedMin p ((n + 1) * M + 1))

/-- Lower square-root approximation, totalized at negative inputs. -/
def sqrtApprox (x : QCode) (t : Nat) : QCode :=
  ⟨Int.ofNat (Nat.sqrt ((x.num.toNat * 2 ^ (2 * t)) / x.den)), 2 ^ t⟩

/-- Leibniz's alternating rational approximation to pi. -/
def piApprox (t : Nat) : QCode :=
  QCode.mul (QCode.ofNat 4)
    (QCode.sum (fun k => ⟨if k % 2 = 0 then 1 else -1, 2 * k + 1⟩)
      (2 ^ (t + 4)))

/-- Rational approximation to the Wikipedia/Lovasz leading expression
    C(n) = (n/W(n))^n * exp(n/W(n)-n-1) / sqrt(W(n)).
    The overprecision is a fixed polynomial in n and t. -/
def growthApprox (n t : Nat) : QCode :=
  let s := t + 8 * (n + 1) ^ 2 + 16
  let r := wApprox n s
  let a := QCode.div (QCode.ofNat n) r
  QCode.div
    (QCode.mul (QCode.pow a n)
      (expApprox (QCode.sub a (QCode.ofNat (n + 1))) s))
    (sqrtApprox r s)

/-- Fixed explicit convergence modulus from the human saddle-point proof. -/
def growthModulus (q : Nat) : Nat := 2 ^ (64 * q ^ 2)

def digit (base code k : Nat) : Nat := code / base ^ k % base

def packedStep (base width code : Nat) : Nat :=
  BellIPRA.sum (fun k =>
    (if k = 0 then 0 else k * digit base code k + digit base code (k - 1))
      * base ^ k) width

def packedRows (base width : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => packedStep base width (packedRows base width n)

/-- A first-order bounded-array program for Bell numbers. -/
def packedBell (n : Nat) : Nat :=
  let base := (n + 2) ^ (n + 2) + 1
  let code := packedRows base (n + 1) n
  BellIPRA.sum (digit base code) (n + 1)

/-- The main definability bridge still to be formally proved. -/
def PackedAgreementTarget : Prop := ∀ n, packedBell n = bell n

def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d, d ≤ p → (p % d = 0 → d = 1 ∨ d = p)

def TouchardTarget : Prop :=
  ∀ p n, Prime p → bell (n + p) % p = (bell n + bell (n + 1)) % p

def primePeriod (p : Nat) : Nat := BellIPRA.sum (fun j => p ^ j) p

def PrimePeriodTarget : Prop :=
  ∀ p n, Prime p → bell (n + primePeriod p) % p = bell n % p

def LogConvexTarget : Prop :=
  ∀ n, bell (n + 1) ^ 2 ≤ bell n * bell (n + 2)

def NormalizedLogConcaveTarget : Prop :=
  ∀ n, (n + 1) * bell n * bell (n + 2) ≤ (n + 2) * bell (n + 1) ^ 2

/-- A purely arithmetic, rationally slackened form of the logarithmic
    Lambert-W estimate. Denominator positivity is proved along the way. -/
def LogLambertTarget : Prop :=
  ∀ n t, 3 ≤ n →
  let r := wApprox n t
  let lhs := QCode.abs (QCode.sub
    (QCode.div (logApprox (QCode.ofNat (bell n)) t) (QCode.ofNat n))
    (QCode.add (QCode.sub r QCode.one) (QCode.inv r)))
  let rhs := QCode.add
    (QCode.div (QCode.add (logApprox (QCode.ofNat n) t) (QCode.ofNat 4))
      (QCode.ofNat n))
    (QCode.mul (QCode.ofNat 8) (QCode.eps t))
  QCode.le lhs rhs

/-- A finite rational target for the leading equivalent, including slack
    for the certified approximation algorithms. This proposition is not
    asserted as a checked theorem by this source file. -/
def WikipediaGrowthTarget : Prop :=
  ∀ q n t, 1 ≤ q → growthModulus q ≤ n →
  let C := growthApprox n (t + 4 * (n + 1) ^ 2 + 8)
  QCode.le
    (QCode.abs (QCode.sub (QCode.div (QCode.ofNat (bell n)) C) QCode.one))
    (QCode.add (QCode.inv (QCode.ofNat q))
      (QCode.mul (QCode.ofNat 4) (QCode.eps t)))

end BellIPRA
