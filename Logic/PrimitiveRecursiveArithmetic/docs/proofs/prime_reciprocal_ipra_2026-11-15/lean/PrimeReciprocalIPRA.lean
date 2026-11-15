/-!
# Constructive divergence of the reciprocal-prime sum in iPRA

This file is a formalization scaffold, not a completed proof.  It is designed
for the ProveIt root workspace at commit
0e834f7851375f4b22ae8892000495cb6fa9eee8 (2026-11-15), with Mathlib v4.32.0
and the `ConciseIPRA` Lean library.

The semantic layer states the finite natural-number inequalities.  The final
section describes the syntactic `PRAAx` theorem and its transfer through
`FromPRA.interp.sound`.  Every `sorry` is paired with a proof obligation in
`FORMALIZATION_PLAN.md`.
-/

import Mathlib
import ConciseIPRA.PR
import ConciseIPRA.PRAToScalar
import ConciseIPRA.Interpretation

set_option autoImplicit false

namespace PrimeReciprocalIPRA

open scoped BigOperators

/-- The finite set of primes at most `n`. -/
def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

/-- `Q_n`: product of all primes at most `n`. -/
def primeProduct (n : ℕ) : ℕ :=
  ∏ p in primesUpTo n, p

/-- `R_n`: numerator of the reciprocal-prime sum over denominator `Q_n`. -/
def primeNumerator (n : ℕ) : ℕ :=
  ∑ p in primesUpTo n, primeProduct n / p

/-- `D_n`: denominator of the finite Euler product. -/
def eulerDenominator (n : ℕ) : ℕ :=
  ∏ p in primesUpTo n, (p - 1)

/-- `T_n`: numerator of the harmonic sum over denominator `n!`. -/
def harmonicNumerator (n : ℕ) : ℕ :=
  ∑ m in Finset.Icc 1 n, Nat.factorial n / m

/-- The explicit primitive-recursive witness. -/
def witness (k : ℕ) : ℕ :=
  2 ^ (2 * 4 ^ k)

/-- Rational semantic presentation of the prime reciprocal partial sum. -/
def primeReciprocalSum (n : ℕ) : ℚ :=
  ∑ p in primesUpTo n, (1 : ℚ) / (p : ℚ)

/-- Rational semantic presentation of the harmonic sum. -/
def harmonicSum (n : ℕ) : ℚ :=
  ∑ m in Finset.Icc 1 n, (1 : ℚ) / (m : ℚ)

/-- Rational semantic presentation of the finite Euler product. -/
def eulerProduct (n : ℕ) : ℚ :=
  ∏ p in primesUpTo n, (p : ℚ) / ((p - 1 : ℕ) : ℚ)

section BasicDenominators

/-- Every selected prime divides the prime product. -/
theorem prime_dvd_primeProduct {n p : ℕ} (hp : p ∈ primesUpTo n) :
    p ∣ primeProduct n := by
  sorry

/-- The denominator-coded numerator agrees with the rational finite sum. -/
theorem primeReciprocalSum_eq (n : ℕ) :
    primeReciprocalSum n =
      (primeNumerator n : ℚ) / (primeProduct n : ℚ) := by
  sorry

/-- The factorial-coded numerator agrees with the rational harmonic sum. -/
theorem harmonicSum_eq (n : ℕ) :
    harmonicSum n =
      (harmonicNumerator n : ℚ) / (Nat.factorial n : ℚ) := by
  sorry

/-- The product denominator agrees with the rational finite Euler product. -/
theorem eulerProduct_eq (n : ℕ) :
    eulerProduct n =
      (primeProduct n : ℚ) / (eulerDenominator n : ℚ) := by
  sorry

end BasicDenominators

section FactorizationAndEuler

/-!
For the semantic Mathlib layer there are two viable implementations.

1. Use `Nat.factorization` to map each `m <= n` to its exponent vector.
2. Define the same bounded least-prime-factor trace intended for the iPRA
   layer, then prove reconstruction and injectivity.

The second route gives more code reuse with the syntactic internalization.
-/

/-- Cross-multiplied finite Euler domination `H_n <= E_n`. -/
theorem harmonicLeEulerCross (n : ℕ) :
    harmonicNumerator n * eulerDenominator n ≤
      Nat.factorial n * primeProduct n := by
  sorry

/-- Rational corollary of `harmonicLeEulerCross`. -/
theorem harmonic_le_euler (n : ℕ) :
    harmonicSum n ≤ eulerProduct n := by
  sorry

end FactorizationAndEuler

section LocalFactor

/-- Finite binomial estimate `(a+1)^a <= 3*a^a`. -/
theorem binomialThreeBound (a : ℕ) (ha : 1 ≤ a) :
    (a + 1) ^ a ≤ 3 * a ^ a := by
  sorry

/-- Integer form of `(p/(p-1))^p <= 4`. -/
theorem localFactorBound (p : ℕ) (hp : 2 ≤ p) :
    p ^ p ≤ 4 * (p - 1) ^ p := by
  sorry

end LocalFactor

section ProductControl

/--
Power-cleared finite-product estimate
`Q_n ^ Q_n <= 4 ^ R_n * D_n ^ Q_n`.
-/
theorem eulerPowerBound (n : ℕ) :
    primeProduct n ^ primeProduct n ≤
      4 ^ primeNumerator n *
        eulerDenominator n ^ primeProduct n := by
  sorry

/-- A putative bound on the reciprocal-prime sum bounds the Euler product. -/
theorem primeProduct_le_of_primeNumerator_le
    (n k : ℕ) (h : primeNumerator n ≤ k * primeProduct n) :
    primeProduct n ≤ 4 ^ k * eulerDenominator n := by
  sorry

/-- Cross-multiplied consequence `H_n <= 4^k`. -/
theorem harmonicNumerator_le_of_primeNumerator_le
    (n k : ℕ) (h : primeNumerator n ≤ k * primeProduct n) :
    harmonicNumerator n ≤ 4 ^ k * Nat.factorial n := by
  sorry

end ProductControl

section DyadicHarmonic

/-- `H_(2^(2t)) >= 1+t`, with the factorial denominator cleared. -/
theorem dyadicHarmonicLower (t : ℕ) :
    (1 + t) * Nat.factorial (2 ^ (2 * t)) ≤
      harmonicNumerator (2 ^ (2 * t)) := by
  sorry

end DyadicHarmonic

section MainSemanticTheorem

/-- The exact natural-number theorem to internalize in `PRAAx`. -/
theorem quantitativeDivergenceNat (k : ℕ) :
    k * primeProduct (witness k) <
      primeNumerator (witness k) := by
  sorry

/-- Rational restatement of the quantitative theorem. -/
theorem quantitativeDivergenceRat (k : ℕ) :
    (k : ℚ) < primeReciprocalSum (witness k) := by
  sorry

/-- Ordinary constructive unboundedness with an explicit witness. -/
theorem reciprocalPrimesUnbounded (k : ℕ) :
    ∃ n : ℕ, (k : ℚ) < primeReciprocalSum n := by
  exact ⟨witness k, quantitativeDivergenceRat k⟩

end MainSemanticTheorem

/-!
## Syntactic iPRA layer

The completed development should add modules under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/` (or a new
lean library) that implement the following objects.

* `ltBPR : PR 2` -- Boolean less-than.
* `primeBPR : PR 1` -- primality characteristic.
* bounded sum/product combinators over `PR` codes.
* `primeProductPR`, `primeNumeratorPR`, `eulerDenominatorPR`,
  `harmonicNumeratorPR`, and `witnessPR`.
* `targetBody : Fm PTm 1`, expressing

      ltB (x * primeProduct (witness x))
          (primeNumerator (witness x)) = 1.

The final standard-iPRA theorem should have the signature

    theorem primeReciprocalDivergencePRA :
      ([] : List (Fm PTm 0)) ⊢[PRAAx] Fm.all targetBody := by
      ...

with every induction instance discharged through `PRA.qfInd`.

The concise scalar result is then one line:

    def primeReciprocalDivergenceTeq :=
      FromPRA.interp.sound primeReciprocalDivergencePRA

The result type is the mapped formula
`(Fm.all targetBody).map FromPRA.morph.f` in `TeqAx`.
-/

end PrimeReciprocalIPRA
