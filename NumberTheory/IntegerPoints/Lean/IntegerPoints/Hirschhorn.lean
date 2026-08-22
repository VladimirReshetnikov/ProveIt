import IntegerPoints.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Hirschhorn, *Partial fractions and four classical theorems of number theory*

Formal statements (no proofs) of the results of

> M. D. Hirschhorn, Partial fractions and four classical theorems of number
> theory, Amer. Math. Monthly 107 (2000), 260–264,

transcribed in
`Papers/Partial fractions and four classical theorems of number theory.tex`.

The paper proves the two-square theorem of Jacobi (1828), Dirichlet's theorem
on `x² + 2y²` (1840), Lorenz's theorem on `x² + 3y²` (1871) and Jacobi's
four-square theorem (1829) from one partial-fractions expansion,
(`eq:infinite-partial-fractions`), together with two special cases of
Jacobi's triple-product identity.  Besides the four theorems we state the
triple-product identity, the two theta-product specialisations, the finite
and infinite partial-fractions expansions (1)–(2), the four `q`-series
identities (3)–(6) obtained from (2), and the four generating-function
identities from which the theorems are read off.

## Conventions

* `divisorCountMod r m n` is `d_{r,m}(n)`, the number of divisors `d` of `n`
  with `d ≡ r (mod m)`.
* `repCount a b n` is the number of `(x, y) ∈ ℤ²` with `a x² + b y² = n`
  (order and signs counted), so `repCount 1 1 = sumTwoSquaresCount`.
* `thetaSeries a q = ∑_{n ∈ ℤ} aⁿ q^{n²}`, so that
  `∑ (-1)ⁿ q^{n²} = thetaSeries (-1) q` and `∑ q^{2n²} = thetaSeries 1 (q²)`.
* `qPochhammer a q n = (a; q)_n`.
* Infinite products and sums are Mathlib's unconditional `∏'` and `∑'`; under
  the hypotheses `|q| < 1`, `|a| < 1` of the paper every series and product
  below converges absolutely, so this is faithful.  Sums `∑_{n ≥ 1}` are
  written as sums over `n : ℕ` of the term at `n + 1`.
-/

open scoped BigOperators
open Real

namespace LeanProofs.IntegerPoints

/-! ### Arithmetic functions -/

/-- `d_{r,m}(n)`: the number of divisors `d` of `n` with `d ≡ r (mod m)`. -/
def divisorCountMod (r m n : ℕ) : ℕ :=
  ((Nat.divisors n).filter fun d => d % m = r).card

/-- The number of representations of `n` as `a x² + b y²` with
`(x, y) ∈ ℤ²` (order and signs counted). -/
noncomputable def repCount (a b : ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)}

/-- The number of representations of `n` as a sum of four integer squares. -/
noncomputable def sumFourSquaresCount (n : ℕ) : ℕ :=
  Set.ncard {p : ℤ × ℤ × ℤ × ℤ |
    p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = (n : ℤ)}

/-- `∑_{d ∣ n, 4 ∤ d} d`, the divisor sum of Jacobi's four-square theorem. -/
def divisorSumNotFour (n : ℕ) : ℕ :=
  ∑ d ∈ (Nat.divisors n).filter (fun d => ¬ 4 ∣ d), d

/-! ### The four classical theorems -/

/-- **Jacobi (1828)**, the two-square theorem: for `n ≥ 1`, the number of
representations of `n` as a sum of two squares is
`4 (d_{1,4}(n) - d_{3,4}(n))`. -/
def hirschhorn_jacobiTwoSquares : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (sumTwoSquaresCount n : ℤ) =
      4 * ((divisorCountMod 1 4 n : ℤ) - (divisorCountMod 3 4 n : ℤ))

/-- **Dirichlet (1840)**: for `n ≥ 1`, the number of representations of `n`
as a square plus twice a square is
`2 (d_{1,8}(n) + d_{3,8}(n) - d_{5,8}(n) - d_{7,8}(n))`. -/
def hirschhorn_dirichlet : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (repCount 1 2 n : ℤ) =
      2 * ((divisorCountMod 1 8 n : ℤ) + (divisorCountMod 3 8 n : ℤ) -
            (divisorCountMod 5 8 n : ℤ) - (divisorCountMod 7 8 n : ℤ))

/-- **Lorenz (1871)**: for `n ≥ 1`, the number of representations of `n` as a
square plus three times a square is
`2 (d_{1,3}(n) - d_{2,3}(n)) + 4 (d_{4,12}(n) - d_{8,12}(n))`. -/
def hirschhorn_lorenz : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (repCount 1 3 n : ℤ) =
      2 * ((divisorCountMod 1 3 n : ℤ) - (divisorCountMod 2 3 n : ℤ)) +
        4 * ((divisorCountMod 4 12 n : ℤ) - (divisorCountMod 8 12 n : ℤ))

/-- **Jacobi (1829)**, the four-square theorem: for `n ≥ 1`, the number of
representations of `n` as a sum of four squares is `8 ∑_{d ∣ n, 4 ∤ d} d`. -/
def hirschhorn_jacobiFourSquares : Prop :=
  ∀ n : ℕ, 1 ≤ n → sumFourSquaresCount n = 8 * divisorSumNotFour n

/-! ### Theta series and `q`-products -/

/-- `∑_{n ∈ ℤ} aⁿ q^{n²}`. -/
noncomputable def thetaSeries (a q : ℂ) : ℂ := ∑' n : ℤ, a ^ n * q ^ (n ^ 2)

/-- The `q`-Pochhammer symbol `(a; q)_n = (1 - a)(1 - a q) ⋯ (1 - a q^{n-1})`. -/
noncomputable def qPochhammer (a q : ℂ) (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

/-- **Jacobi's triple-product identity**: for `a ≠ 0` and `|q| < 1`,
`∏_{n ≥ 1} (1 + a q^{2n-1})(1 + a⁻¹ q^{2n-1})(1 - q^{2n}) = ∑_{n ∈ ℤ} aⁿ q^{n²}`. -/
def jacobiTripleProduct : Prop :=
  ∀ a q : ℂ, a ≠ 0 → ‖q‖ < 1 →
    (∏' n : ℕ, ((1 + a * q ^ (2 * n + 1)) * (1 + a⁻¹ * q ^ (2 * n + 1)) *
        (1 - q ^ (2 * n + 2)))) = thetaSeries a q

/-- The specialisation `a = -1` of the triple product:
`∑ (-1)ⁿ q^{n²} = ∏_{n ≥ 1} (1 - qⁿ)/(1 + qⁿ)` for `|q| < 1`. -/
def hirschhorn_thetaMinusOne : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries (-1) q = ∏' n : ℕ, ((1 - q ^ (n + 1)) / (1 + q ^ (n + 1)))

/-- The substitution `q ↦ -q²` in the previous identity:
`∑ q^{2n²} = ∏_{n ≥ 1} (1 + q^{4n-2})(1 - q^{4n}) / ((1 + q^{4n})(1 - q^{4n-2}))`
for `|q| < 1`. -/
def hirschhorn_thetaTwoSquare : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries 1 (q ^ 2) =
      ∏' n : ℕ, (((1 + q ^ (4 * n + 2)) * (1 - q ^ (4 * n + 4))) /
        ((1 + q ^ (4 * n + 4)) * (1 - q ^ (4 * n + 2))))

/-! ### The partial-fractions expansions (1) and (2) -/

/-- `A₀ = (a; q)_N² / (q; q)_N²` of (1). -/
noncomputable def hirschhornA0 (a q : ℂ) (N : ℕ) : ℂ :=
  qPochhammer a q N ^ 2 / qPochhammer q q N ^ 2

/-- `A_n = aⁿ (a⁻¹ q; q)_n (1 + qⁿ) / (a; q)_n ·
(a; q)_{N+n} (a; q)_{N-n} / ((q; q)_{N+n} (q; q)_{N-n})` of (1), for `n ≥ 1`. -/
noncomputable def hirschhornA (a q : ℂ) (N n : ℕ) : ℂ :=
  a ^ n * qPochhammer (a⁻¹ * q) q n * (1 + q ^ n) / qPochhammer a q n *
    (qPochhammer a q (N + n) * qPochhammer a q (N - n) /
      (qPochhammer q q (N + n) * qPochhammer q q (N - n)))

/-- **(1)**, the finite partial-fractions expansion: provided no denominator
vanishes (the `a⁻¹` in `(a⁻¹ q; q)_n` requires `a ≠ 0`; with Lean's `0⁻¹ = 0`
the identity would fail at `a = 0`),
`(2 - x)⁻¹ ∏_{n=1}^{N} (1 - a q^{n-1} x + a² q^{2n-2}) / (1 - qⁿ x + q^{2n})
   = A₀ / (2 - x) + ∑_{n=1}^{N} A_n / (1 - qⁿ x + q^{2n})`. -/
def hirschhorn_finitePartialFractions : Prop :=
  ∀ (N : ℕ) (a q x : ℂ), a ≠ 0 → x ≠ 2 →
    (∀ n ∈ Finset.Icc 1 N, 1 - q ^ n * x + q ^ (2 * n) ≠ 0) →
    qPochhammer a q (2 * N) ≠ 0 → qPochhammer q q (2 * N) ≠ 0 →
    (1 / (2 - x)) * ∏ n ∈ Finset.Icc 1 N,
        ((1 - a * q ^ (n - 1) * x + a ^ 2 * q ^ (2 * n - 2)) / (1 - q ^ n * x + q ^ (2 * n)))
      = hirschhornA0 a q N / (2 - x) +
          ∑ n ∈ Finset.Icc 1 N, hirschhornA a q N n / (1 - q ^ n * x + q ^ (2 * n))

/-- **(2)**, the infinite partial-fractions expansion: for `0 < |a| < 1`,
`|q| < 1`, and no vanishing denominator,
`(2 - x)⁻¹ ∏_{n ≥ 1} (1 - a q^{n-1} x + a² q^{2n-2}) / (1 - qⁿ x + q^{2n}) ·
   (1 - qⁿ)² / (1 - a q^{n-1})²
 = (2 - x)⁻¹ + ∑_{n ≥ 1} aⁿ (a⁻¹ q; q)_n (1 + qⁿ) / ((a; q)_n (1 - qⁿ x + q^{2n}))`. -/
def hirschhorn_infinitePartialFractions : Prop :=
  ∀ a q x : ℂ, 0 < ‖a‖ → ‖a‖ < 1 → ‖q‖ < 1 → x ≠ 2 →
    (∀ n : ℕ, 1 - q ^ (n + 1) * x + q ^ (2 * (n + 1)) ≠ 0) →
    (∀ n : ℕ, 1 - a * q ^ n ≠ 0) →
    (1 / (2 - x)) * ∏' n : ℕ,
        ((1 - a * q ^ n * x + a ^ 2 * q ^ (2 * n)) / (1 - q ^ (n + 1) * x + q ^ (2 * (n + 1))) *
          ((1 - q ^ (n + 1)) ^ 2 / (1 - a * q ^ n) ^ 2))
      = 1 / (2 - x) +
          ∑' n : ℕ, a ^ (n + 1) * qPochhammer (a⁻¹ * q) q (n + 1) * (1 + q ^ (n + 1)) /
            (qPochhammer a q (n + 1) * (1 - q ^ (n + 1) * x + q ^ (2 * (n + 1))))

/-! ### The four `q`-series identities (3)–(6) -/

/-- **(3)** (`a = -q`, `x = 0` in (2)): for `|q| < 1`,
`(∑ (-1)ⁿ q^{n²})² = 1 + 4 ∑_{n ≥ 1} (-1)ⁿ qⁿ / (1 + q^{2n})`. -/
def hirschhorn_twoSquaresBase : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries (-1) q ^ 2 =
      1 + 4 * ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * q ^ (n + 1) / (1 + q ^ (2 * (n + 1)))

/-- **(4)** (`a = -q`, `x = -2` in (2)): for `|q| < 1`,
`(∑ (-1)ⁿ q^{n²})⁴ = 1 + 8 ∑_{n ≥ 1} (-1)ⁿ qⁿ / (1 + qⁿ)²`. -/
def hirschhorn_fourSquaresBase : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries (-1) q ^ 4 =
      1 + 8 * ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * q ^ (n + 1) / (1 + q ^ (n + 1)) ^ 2

/-- **(5)** (`a = -q`, `x = 1` in (2)): for `|q| < 1`,
`(∑ (-1)ⁿ q^{n²}) (∑ (-1)ⁿ q^{3n²}) = 1 + 2 ∑_{n ≥ 1} (-1)ⁿ qⁿ / (1 - qⁿ + q^{2n})`. -/
def hirschhorn_lorenzBase : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries (-1) q * thetaSeries (-1) (q ^ 3) =
      1 + 2 * ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * q ^ (n + 1) /
        (1 - q ^ (n + 1) + q ^ (2 * (n + 1)))

/-- **(6)** (`q ↦ q²`, `a = -q`, `x = 0` in (2)): for `|q| < 1`,
`(∑ q^{2n²}) (∑ (-1)ⁿ q^{n²}) = 1 + 2 ∑_{n ≥ 1} (-1)ⁿ qⁿ (1 + q^{2n}) / (1 + q^{4n})`. -/
def hirschhorn_dirichletBase : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries 1 (q ^ 2) * thetaSeries (-1) q =
      1 + 2 * ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * q ^ (n + 1) * (1 + q ^ (2 * (n + 1))) /
        (1 + q ^ (4 * (n + 1)))

/-! ### The generating-function forms of the four theorems -/

/-- `(∑ q^{n²})² = 1 + 4 ∑_{n ≥ 1} (d_{1,4}(n) - d_{3,4}(n)) qⁿ` for `|q| < 1`. -/
def hirschhorn_twoSquaresGenerating : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries 1 q ^ 2 =
      1 + 4 * ∑' n : ℕ,
        ((divisorCountMod 1 4 (n + 1) : ℂ) - (divisorCountMod 3 4 (n + 1) : ℂ)) * q ^ (n + 1)

/-- `(∑ q^{n²})⁴ = 1 + 8 ∑_{n ≥ 1} (∑_{d ∣ n, 4 ∤ d} d) qⁿ` for `|q| < 1`. -/
def hirschhorn_fourSquaresGenerating : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries 1 q ^ 4 =
      1 + 8 * ∑' n : ℕ, (divisorSumNotFour (n + 1) : ℂ) * q ^ (n + 1)

/-- `(∑ q^{n²}) (∑ q^{3n²}) = 1 + 2 ∑_{n ≥ 1} (d_{1,3}(n) - d_{2,3}(n)) qⁿ
  + 4 ∑_{n ≥ 1} (d_{4,12}(n) - d_{8,12}(n)) qⁿ` for `|q| < 1`. -/
def hirschhorn_lorenzGenerating : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries 1 q * thetaSeries 1 (q ^ 3) =
      1 + 2 * ∑' n : ℕ,
            ((divisorCountMod 1 3 (n + 1) : ℂ) - (divisorCountMod 2 3 (n + 1) : ℂ)) * q ^ (n + 1)
        + 4 * ∑' n : ℕ,
            ((divisorCountMod 4 12 (n + 1) : ℂ) - (divisorCountMod 8 12 (n + 1) : ℂ)) *
              q ^ (n + 1)

/-- `(∑ q^{n²}) (∑ q^{2n²})
  = 1 + 2 ∑_{n ≥ 1} (d_{1,8}(n) + d_{3,8}(n) - d_{5,8}(n) - d_{7,8}(n)) qⁿ` for `|q| < 1`. -/
def hirschhorn_dirichletGenerating : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 →
    thetaSeries 1 q * thetaSeries 1 (q ^ 2) =
      1 + 2 * ∑' n : ℕ,
        ((divisorCountMod 1 8 (n + 1) : ℂ) + (divisorCountMod 3 8 (n + 1) : ℂ) -
          (divisorCountMod 5 8 (n + 1) : ℂ) - (divisorCountMod 7 8 (n + 1) : ℂ)) * q ^ (n + 1)

end LeanProofs.IntegerPoints
