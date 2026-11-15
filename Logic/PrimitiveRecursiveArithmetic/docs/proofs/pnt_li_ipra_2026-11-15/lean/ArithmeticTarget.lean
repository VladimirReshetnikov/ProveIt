import Mathlib

/-!
# Exact arithmetic specification for the logarithmic-integral PNT

STATUS: UNCOMPILED OUTLINE. There is no Lean executable in the construction
environment. This file contains definitions and an explicitly parameterized
input contract. It contains no proof of the prime number theorem.

The functions deliberately use structurally bounded recursions. They are a
specification to compile to ConciseIPRA.PR, not already such a compilation.
They are not intended for efficient large-scale numerical evaluation.

The notation `logLower u v` matches the accompanying Python/manuscript:
range reduction u = 2^e r, 1 <= r < 2; N = v + e + 2; atanh series length N.
For inputs u < 1 we use the harmless totalization value zero.
-/

namespace LiPNT.Arithmetic

/-- A finite rational sum, with an explicit natural-number bound. -/
def qsum (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => qsum f n + f n

/-- Tests all potential proper divisors up to the supplied finite bound. -/
def noProperDivisors (n : ℕ) : ℕ → Bool
  | 0 => true
  | d + 1 =>
      if 2 ≤ d + 1 ∧ d + 1 < n ∧ n % (d + 1) = 0 then
        false
      else
        noProperDivisors n d

/-- An elementary bounded-divisibility specification of the prime flag. -/
def primeFlag (n : ℕ) : ℕ :=
  if 2 ≤ n ∧ noProperDivisors n n = true then 1 else 0

/-- Counts primes at most n, once primeFlag is proved equivalent to primality. -/
def primeCount : ℕ → ℕ
  | 0 => 0
  | n + 1 => primeCount n + primeFlag (n + 1)

/-- Bounded search for the binary length. The search argument is explicit. -/
def bitScan (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if 2 ^ k ≤ n then k + 1 else bitScan n k

def bitLength (n : ℕ) : ℕ := bitScan n (n + 1)

/-- Finds the largest e below the search bound for which 2^e <= u. -/
def exponentScan (u : ℚ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if (2 : ℚ) ^ k ≤ u then k else exponentScan u k

/-- For u >= 1 its numerator gives a valid, deliberately crude search bound. -/
def rationalBinaryExponent (u : ℚ) : ℕ :=
  exponentScan u (u.num.natAbs + 1)

/-- Truncated 2 atanh((r-1)/(r+1)) series. -/
def atanhLogSum (r : ℚ) (N : ℕ) : ℚ :=
  let z := (r - 1) / (r + 1)
  2 * qsum (fun i => z ^ (2 * i + 1) / (2 * i + 1 : ℕ)) N

/-- A lower logarithm approximation; on u >= 1 its error is <= 2^(-v). -/
def logLower (u : ℚ) (v : ℕ) : ℚ :=
  if u < 1 then 0 else
    let e := rationalBinaryExponent u
    let r := u / (2 : ℚ) ^ e
    let N := v + e + 2
    (e : ℚ) * atanhLogSum 2 N + atanhLogSum r N

/-- A finite lower approximation to theta, with error at most n * 2^(-v). -/
def thetaLower (n v : ℕ) : ℚ :=
  qsum (fun j => (primeFlag j : ℚ) * logLower (j : ℚ) v) (n + 1)

/-- The exact left-endpoint rational Riemann sum in the manuscript. -/
def liApprox (n v : ℕ) : ℚ :=
  if n < 2 then 0 else
    let h : ℚ := 1 / (2 : ℚ) ^ (v + 3)
    let J : ℕ := (n - 2) * 2 ^ (v + 3)
    let P : ℕ := v + bitLength n + 6
    h * qsum (fun j => 1 / logLower (2 + (j : ℚ) * h) P) J

def thetaConstant : ℕ := 2 ^ 240

/-- The exponent in the theta input threshold. -/
def thetaThresholdExponent (r : ℕ) : ℕ :=
  thetaConstant * (r + 1) ^ 10

/-- The exponent in the final binary-length-normalized target threshold. -/
def thresholdExponent (m : ℕ) : ℕ :=
  (2 * thetaConstant) * (m + 7) ^ 10

/-- Expository only: do not attempt to evaluate this astronomical number. -/
def threshold (m : ℕ) : ℕ := 2 ^ thresholdExponent m

/-!
The next proposition is the exact denominator-cleared matrix.
If A = a/d = liApprox n v and b = bitLength n, it reads

  |d*pi(n) - a| * 2^(m+v) * b <= d * (n*2^v + 2^m*b).

For n >= 2 this is equivalent to

  |pi(n) - A(n,v)| <= n/(2^m*b(n)) + 2^(-v).

The equivalence still has to be proved in the completed development.
-/

def integerMatrix (m n v : ℕ) : Prop :=
  let A := liApprox n v
  let d : ℕ := A.den
  let z : ℕ := Int.natAbs (((d * primeCount n : ℕ) : ℤ) - A.num)
  let b := bitLength n
  z * 2 ^ (m + v) * b ≤ d * (n * 2 ^ v + 2 ^ m * b)

instance (m n v : ℕ) : Decidable (integerMatrix m n v) := by
  unfold integerMatrix
  infer_instance

/-- The total three-input checker, returning 1 on out-of-range inputs.
The threshold gate uses binary length, so it does not evaluate threshold m.
One must prove thresholdExponent m < bitLength n iff threshold m <= n. -/
def liPntCheck (m n v : ℕ) : ℕ :=
  if n < 2 then 1 else
    if bitLength n ≤ thresholdExponent m then 1 else
      if integerMatrix m n v then 1 else 0

/-- A statement to prove, not a theorem asserted by this file. -/
def ArithmeticTarget : Prop := ∀ m n v : ℕ, liPntCheck m n v = 1

/-- Explicitly parameterized finite-precision contract for the hard input.
No inhabitant is supplied here. In the completed development F is thetaLower,
and both its correctness and the displayed estimate must be proved. -/
structure ThetaModulusHypothesis (F : ℕ → ℕ → ℚ) : Prop where
  estimate : ∀ r n v : ℕ,
    2 ≤ n → thetaThresholdExponent r < bitLength n →
    |F n v - (n : ℚ)| ≤ (n : ℚ) / (2 : ℚ) ^ r + (n : ℚ) / (2 : ℚ) ^ v

end LiPNT.Arithmetic
