import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Set.Card
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.Coprime.Basic

/-!
# Integer points in circles: shared definitions

Definitions shared by the formal statements of

* W. Zhai and X. Cao, *On the number of coprime integer pairs within a
  circle*, Acta Arith. 90 (1999), 1–16, and
* J. Wu, *On the primitive circle problem*, Monatsh. Math. 135 (2002), 69–81.

The sources are the OCR transcriptions in
`NumberTheory/IntegerPoints/Papers/*.tex`.

## Conventions

* `latticeCount x` is the classical `P(x)`, the number of `(a, b) ∈ ℤ²` with
  `a² + b² ≤ x`, and `circleError x = P(x) - π x` is the error term `E(x)` of
  the circle problem.
* `coprimeLatticeCount x` is `V(x)`, the number of such pairs with
  `gcd(a, b) = 1`, and `primitiveCircleError x = V(x) - (6/π) x` is the
  error term written `E_P(x)` by Zhai–Cao and `Δ(x)` by Wu.
* `e t = exp(2 π i t)`.
* `sumTwoSquaresCount n` is `r(n)`, the number of representations of `n` as
  `a² + b²` with `(a, b) ∈ ℤ²` (order and signs counted).
* `intRange A B` is the set of integers `n` with `A < n ≤ B`, and
  `dyadic M = intRange M (2 M)` is the dyadic block `m ∼ M`, i.e.
  `M < m ≤ 2 M`.  Wu uses exactly this meaning of `m ∼ M`; Zhai–Cao write
  `m ∼ M` for `c₁ M ≤ m ≤ c₂ M` with unspecified absolute constants, and we
  specialise their statements to the dyadic block as well.
* `nearestIntDist t = ‖t‖` is the distance from `t` to the nearest integer.

Since `1 / 0 = 0` in Lean, the quantities `min (D, 1 / ‖t‖)` that occur in the
lemmas are written with the helper `minInv`, which returns `D` when `‖t‖ = 0`
(the intended value `min (D, +∞)`).
-/

open scoped BigOperators
open Real

namespace LeanProofs.IntegerPoints

/-- `e(t) = exp(2 π i t)`. -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The integers `n` with `A < n ≤ B`, as a finset of naturals.  For `A ≥ 0`
this is exactly the set of positive integers in `(A, B]`. -/
noncomputable def intRange (A B : ℝ) : Finset ℕ := Finset.Ioc ⌊A⌋₊ ⌊B⌋₊

/-- The dyadic block `m ∼ M`, i.e. `M < m ≤ 2 M`. -/
noncomputable def dyadic (M : ℝ) : Finset ℕ := intRange M (2 * M)

/-- The positive integers `m ≤ y`. -/
noncomputable def upTo (y : ℝ) : Finset ℕ := Finset.Icc 1 ⌊y⌋₊

/-- Distance from `t` to the nearest integer, written `‖t‖` in the papers. -/
noncomputable def nearestIntDist (t : ℝ) : ℝ := |t - round t|

/-- `min (D, 1 / t)` with the convention `1 / 0 = +∞`, so the value is `D`
when `t = 0`. -/
noncomputable def minInv (D t : ℝ) : ℝ := if t = 0 then D else min D (1 / t)

/-- `P(x)`: the number of integer points `(a, b)` with `a² + b² ≤ x`. -/
noncomputable def latticeCount (x : ℝ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ x}

/-- `E(x) = P(x) - π x`: the error term of the classical circle problem. -/
noncomputable def circleError (x : ℝ) : ℝ := (latticeCount x : ℝ) - Real.pi * x

/-- `V(x)`: the number of coprime integer pairs `(a, b)` with `a² + b² ≤ x`. -/
noncomputable def coprimeLatticeCount (x : ℝ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ≤ x ∧ IsCoprime p.1 p.2}

/-- `E_P(x) = Δ(x) = V(x) - (6/π) x`: the error term of the primitive circle
problem. -/
noncomputable def primitiveCircleError (x : ℝ) : ℝ :=
  (coprimeLatticeCount x : ℝ) - 6 / Real.pi * x

/-- `r(n)`: the number of representations of `n` as a sum of two integer
squares. -/
noncomputable def sumTwoSquaresCount (n : ℕ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 2 = (n : ℤ)}

/-- The Möbius function as a complex number. -/
noncomputable def moebiusC (n : ℕ) : ℂ := (ArithmeticFunction.moebius n : ℂ)

/-- The Möbius function as a real number. -/
noncomputable def moebiusR (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ)

/-- The weighted exponential sum
`ℛ(M, N) = Σ_{m ∼ M} μ(m) m^{-1/2} Σ_{n ∼ N} r(n) n^{-3/4} e(√(x n) / m)`
of Wu's (1.3); the same sums (without the weights) are the `T(M, N)` of
Zhai–Cao. -/
noncomputable def RSum (x M N : ℝ) : ℂ :=
  ∑ m ∈ dyadic M, ∑ n ∈ dyadic N,
    moebiusC m / ((m : ℝ) ^ ((1 : ℝ) / 2) : ℝ) *
      ((sumTwoSquaresCount n : ℝ) / ((n : ℝ) ^ ((3 : ℝ) / 4)) : ℝ) *
      e (Real.sqrt (x * n) / m)

end LeanProofs.IntegerPoints
