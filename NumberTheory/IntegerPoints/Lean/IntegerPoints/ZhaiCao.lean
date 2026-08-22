import IntegerPoints.ExponentialSums
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Zhai–Cao, *On the number of coprime integer pairs within a circle*

Formal statements (no proofs yet) of the results of

> W. Zhai and X. Cao, On the number of coprime integer pairs within a circle,
> Acta Arith. 90 (1999), 1–16,

transcribed in `Papers/On the number of coprime integer pairs within a circle.tex`.
The general exponential-sum lemmas of their §2 (Lemmas 1–8) are in
`IntegerPoints.ExponentialSums`; this module contains the results specific to
the primitive circle problem: the cited background (1.1)–(1.3), Lemmas 9–10,
Propositions 1–2, and the main Theorem (1.4).

Every statement is a `Prop`-valued definition; nothing is asserted.  The
Riemann Hypothesis is Mathlib's `RiemannHypothesis`.
-/

open scoped BigOperators
open Real Finset Filter Asymptotics

namespace LeanProofs.IntegerPoints

/-! ### Cited background, §1 -/

/-- **(1.1)** (Huxley): `E(x) = O(x^{23/73 + ε})`. -/
def huxley_circleBound : Prop :=
  ∀ ε : ℝ, 0 < ε → circleError =O[atTop] fun x : ℝ => x ^ ((23 : ℝ) / 73 + ε)

/-- **(1.2)** (unconditional, as printed by Zhai–Cao):
`V(x) = (6/π) x + O(x^{1/2} exp(-c log^{3/5} x (log log x)^{-2/5}))` for some
absolute `c > 0`.  (Wu prints the standard Vinogradov–Korobov exponent
`(log log x)^{-1/5}`; see `wu_unconditionalBound`.) -/
def zhaiCao_unconditionalBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    primitiveCircleError =O[atTop] fun x : ℝ =>
      x ^ ((1 : ℝ) / 2) *
        Real.exp (-c * Real.log x ^ ((3 : ℝ) / 5) * Real.log (Real.log x) ^ (-(2 : ℝ) / 5))

/-- **(1.3)** (Nowak): under RH, `V(x) = (6/π) x + O(x^{15/38 + ε})`. -/
def nowak_primitiveCircleBound : Prop :=
  RiemannHypothesis →
    ∀ ε : ℝ, 0 < ε → primitiveCircleError =O[atTop] fun x : ℝ => x ^ ((15 : ℝ) / 38 + ε)

/-! ### The main theorem, (1.4) -/

/-- **Zhai–Cao, Theorem**: if RH is true then
`V(x) = (6/π) x + O(x^{11/30 + ε})`. -/
def zhaiCao_theorem : Prop :=
  RiemannHypothesis →
    ∀ ε : ℝ, 0 < ε → primitiveCircleError =O[atTop] fun x : ℝ => x ^ ((11 : ℝ) / 30 + ε)

/-! ### §2, Lemmas 9–10 and Proposition 1 -/

/-- The triple sum `S = ∑_{n ∼ N} a_n ∑_{u ∼ U} b_u ∑_{v ∼ V} c_v e(√(n x) / (u v))`
of Zhai–Cao, (2.1). -/
noncomputable def tripleSumZC (x N U V : ℝ) (a b c : ℕ → ℂ) : ℂ :=
  ∑ n ∈ dyadic N, ∑ u ∈ dyadic U, ∑ v ∈ dyadic V,
    a n * b u * c v * e (Real.sqrt (n * x) / (u * v))

/-- **Zhai–Cao, Lemma 9**.  For `x` large, positive integers `M, N, U` with
`1 ≤ N ≤ M^{1/4}`, `x^ε ≤ M ≤ x^{4/15}`, `M^{1/6} ≤ U ≤ M^{5/6}`, and
`|a_n|, |b_u|, |c_v| ≤ 1`,
`∑_{n ∼ N} a_n ∑_{u ∼ U} b_u ∑_{v ∼ M/U} c_v e(√(nx)/(uv))
   ≪ (x^{1/12} M^{7/12} N^{11/12} + M^{11/12} N^{1/2}) log x`. -/
def zhaiCao_lemma9 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C x₀ : ℝ, ∀ (x : ℝ) (M N U : ℕ) (a b c : ℕ → ℂ), x₀ ≤ x →
      1 ≤ N → (N : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 4) →
      x ^ ε ≤ M → (M : ℝ) ≤ x ^ ((4 : ℝ) / 15) →
      (M : ℝ) ^ ((1 : ℝ) / 6) ≤ U → (U : ℝ) ≤ (M : ℝ) ^ ((5 : ℝ) / 6) →
      UnitBounded a → UnitBounded b → UnitBounded c →
      ‖tripleSumZC x N U ((M : ℝ) / U) a b c‖ ≤
        C * ((x ^ ((1 : ℝ) / 12) * (M : ℝ) ^ ((7 : ℝ) / 12) * (N : ℝ) ^ ((11 : ℝ) / 12) +
              (M : ℝ) ^ ((11 : ℝ) / 12) * (N : ℝ) ^ ((1 : ℝ) / 2)) * Real.log x)

/-- The sum `T(M, N) = ∑_{n ∼ N} a(n) ∑_{m ∼ M} μ(m) e(√(n x) / m)` of
Zhai–Cao, (2.7). -/
noncomputable def TSum (x M N : ℝ) (a : ℕ → ℂ) : ℂ :=
  ∑ n ∈ dyadic N, a n * ∑ m ∈ dyadic M, moebiusC m * e (Real.sqrt (n * x) / m)

/-- **Zhai–Cao, Lemma 10**.  Under the conditions of Lemma 9 on `x, M, N`
(with `ε₁` in `x^{ε₁} ≤ M`) and `|a(n)| ≤ 1`,
`T(M, N) ≪ (x^{1/12} M^{7/12} N^{11/12} + M^{11/12} N^{1/2}) x^ε`. -/
def zhaiCao_lemma10 : Prop :=
  ∀ ε₁ ε : ℝ, 0 < ε₁ → 0 < ε →
    ∃ C x₀ : ℝ, ∀ (x : ℝ) (M N : ℕ) (a : ℕ → ℂ), x₀ ≤ x →
      1 ≤ N → (N : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 4) →
      x ^ ε₁ ≤ M → (M : ℝ) ≤ x ^ ((4 : ℝ) / 15) → UnitBounded a →
      ‖TSum x M N a‖ ≤
        C * ((x ^ ((1 : ℝ) / 12) * (M : ℝ) ^ ((7 : ℝ) / 12) * (N : ℝ) ^ ((11 : ℝ) / 12) +
              (M : ℝ) ^ ((11 : ℝ) / 12) * (N : ℝ) ^ ((1 : ℝ) / 2)) * x ^ ε)

/-- The bilinear monomial sum
`S = ∑_{M < m ≤ 2M} ∑_{N < n ≤ 2N} a(m) b(n) e(A m^α n^β)` of Zhai–Cao,
Proposition 1. -/
noncomputable def monomialDoubleSum (A α β M N : ℝ) (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ dyadic M, ∑ n ∈ dyadic N, a m * b n * e (A * (m : ℝ) ^ α * (n : ℝ) ^ β)

/-- **Zhai–Cao, Proposition 1**.  Let `α, β` be rational numbers, neither a
non-negative integer, `A > 0`, `M, N` large, `F = A M^α N^β ≫ N`, and
`|a(m)|, |b(n)| ≤ 1`.  Then
`S ≪ (M N^{1/2} + F^{4/20} M^{13/20} N^{15/20} + F^{4/23} M^{15/23} N^{18/23}
      + F^{1/6} M^{2/3} N^{7/9} + F^{1/5} M^{3/5} N^{4/5} + F^{1/10} M^{4/5} N^{7/10}) log⁴ F`. -/
def zhaiCao_prop1 : Prop :=
  ∀ (α β : ℚ) (c : ℝ), (∀ k : ℕ, α ≠ k) → (∀ k : ℕ, β ≠ k) → 0 < c →
    ∃ C M₀ : ℝ, ∀ (A M N : ℝ) (a b : ℕ → ℂ), 0 < A → M₀ ≤ M → M₀ ≤ N →
      c * N ≤ A * M ^ (α : ℝ) * N ^ (β : ℝ) → UnitBounded a → UnitBounded b →
      ‖monomialDoubleSum A α β M N a b‖ ≤
        C * ((M * N ^ ((1 : ℝ) / 2) +
              (A * M ^ (α : ℝ) * N ^ (β : ℝ)) ^ ((4 : ℝ) / 20) *
                M ^ ((13 : ℝ) / 20) * N ^ ((15 : ℝ) / 20) +
              (A * M ^ (α : ℝ) * N ^ (β : ℝ)) ^ ((4 : ℝ) / 23) *
                M ^ ((15 : ℝ) / 23) * N ^ ((18 : ℝ) / 23) +
              (A * M ^ (α : ℝ) * N ^ (β : ℝ)) ^ ((1 : ℝ) / 6) *
                M ^ ((2 : ℝ) / 3) * N ^ ((7 : ℝ) / 9) +
              (A * M ^ (α : ℝ) * N ^ (β : ℝ)) ^ ((1 : ℝ) / 5) *
                M ^ ((3 : ℝ) / 5) * N ^ ((4 : ℝ) / 5) +
              (A * M ^ (α : ℝ) * N ^ (β : ℝ)) ^ ((1 : ℝ) / 10) *
                M ^ ((4 : ℝ) / 5) * N ^ ((7 : ℝ) / 10)) *
          Real.log (A * M ^ (α : ℝ) * N ^ (β : ℝ)) ^ 4)

/-! ### §3, Proposition 2 -/

/-- The Möbius-weighted sum of circle-problem error terms
`∑_{m ≤ y} μ(m) E(x / m²)`. -/
noncomputable def moebiusCircleErrorSum (x y : ℝ) : ℝ :=
  ∑ m ∈ upTo y, moebiusR m * circleError (x / (m : ℝ) ^ 2)

/-- **Zhai–Cao, Proposition 2**, (3.15).  If RH is true then for
`x^ε ≤ y ≤ x^{1/2 - ε}`,
`E_P(x) = ∑_{m ≤ y} μ(m) E(x/m²) + O(y^{-1/2} x^{1/2 + ε})`. -/
def zhaiCao_prop2 : Prop :=
  RiemannHypothesis →
    ∀ ε : ℝ, 0 < ε →
      ∃ C x₀ : ℝ, ∀ x y : ℝ, x₀ ≤ x → x ^ ε ≤ y → y ≤ x ^ ((1 : ℝ) / 2 - ε) →
        |primitiveCircleError x - moebiusCircleErrorSum x y| ≤
          C * (y ^ (-(1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2 + ε))

end LeanProofs.IntegerPoints
