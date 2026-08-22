import IntegerPoints.LittlewoodWalfisz
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Defs.Filter

/-!
# Berndt–Kim–Zaharescu, *The circle problem of Gauss and the divisor problem of Dirichlet — still unsolved*

Formal statements (no proofs) of every numbered theorem, entry, corollary and
quoted result of the survey

> B. C. Berndt, S. Kim and A. Zaharescu, The circle problem of Gauss and the
> divisor problem of Dirichlet—still unsolved, Amer. Math. Monthly 125 (2018),
> 99–114,

transcribed in
`Papers/The Circle Problem of Gauss and the Divisor Problem of Dirichlet - Still Unsolved.tex`.
Results quoted from the literature are stated faithfully as they appear in
the survey.

## Conventions

* `r₂(n)` is `sumTwoSquaresCount n` (so `r₂(0) = 1`), `d(n)` is
  `numDivisors n`.
* The primed sums `∑'_{0 ≤ n ≤ x} r₂(n)` and `∑'_{n ≤ x} d(n)` (half weight
  at `n = x` when `x` is an integer) are `circleSumPrime x` and
  `divisorSumPrime x`; `P(x) = circleSumPrime x - π x` is
  `circleErrorPrime x` and `Δ(x)` of (3.1) is `divisorErrorPrime x`.
* Bessel functions are not in Mathlib.  `besselJC ν z` is the series (2.2)
  with principal powers; `besselYC`, `besselKC` are (3.4), (3.5), with the
  integer-order case defined as the limit `ν → n` as the survey prescribes;
  `besselJ`, `besselY`, `besselK` are the real parts for real order and
  positive real argument (where the complex values are real); `voronoiI` is
  the function `I_ν = -Y_ν - (2/π) K_ν` of (3.7).
* The Bessel series (2.4), (2.5), (3.6), (6.4), (6.5), (6.7) converge only
  conditionally.  `HasOrderedSum f L` says the partial sums
  `∑_{n < N} f n` converge to `L`; sums `∑_{n ≥ 1}` are written as ordered
  sums of the term at `n + 1`.  Iterated double sums are written with an
  explicit sequence of inner sums.
* `O`-results are Mathlib's `=O[atTop]` or explicit constants; the
  survey's `Ω`, `Ω₊`, `Ω₋`, `Ω±` are `IsOmega`, `IsOmegaPlus`, `IsOmegaMinus`,
  `IsOmegaPM`, with "a sequence `xₙ → ∞`" rendered as `∃ᶠ x in atTop`.
* `F(x)` of (6.3) is `endpointFloor x`.
-/

open scoped BigOperators
open Real Finset Filter Asymptotics MeasureTheory

namespace LeanProofs.IntegerPoints

/-! ### Counting functions and error terms -/

open Classical in
/-- `R(x) = ∑'_{0 ≤ n ≤ x} r₂(n)` of (2.1): only `½ r₂(x)` is counted when
`x` is an integer. -/
noncomputable def circleSumPrime (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (⌊x⌋₊ + 1), (sumTwoSquaresCount n : ℝ)) -
    if (⌊x⌋₊ : ℝ) = x then (sumTwoSquaresCount ⌊x⌋₊ : ℝ) / 2 else 0

/-- `P(x) = R(x) - π x`, the error term of the circle problem, (2.1). -/
noncomputable def circleErrorPrime (x : ℝ) : ℝ := circleSumPrime x - Real.pi * x

open Classical in
/-- `D(x) = ∑'_{n ≤ x} d(n)` of (3.1): only `½ d(x)` is counted when `x` is
an integer. -/
noncomputable def divisorSumPrime (x : ℝ) : ℝ :=
  (∑ n ∈ upTo x, (numDivisors n : ℝ)) -
    if (⌊x⌋₊ : ℝ) = x then (numDivisors ⌊x⌋₊ : ℝ) / 2 else 0

/-- `Δ(x) = D(x) - x (log x + 2γ - 1) - 1/4`, the error term of the divisor
problem, (3.1). -/
noncomputable def divisorErrorPrime (x : ℝ) : ℝ :=
  divisorSumPrime x -
    (x * (Real.log x + 2 * Real.eulerMascheroniConstant - 1) + 1 / 4)

/-! ### Bessel functions -/

/-- **(2.2)**: `J_ν(z) = ∑_{n ≥ 0} (-1)ⁿ / (n! Γ(ν + n + 1)) (z/2)^{ν + 2n}`, with
principal powers. -/
noncomputable def besselJC (ν z : ℂ) : ℂ :=
  ∑' n : ℕ, ((-1 : ℂ) ^ n / ((Nat.factorial n : ℂ) * Complex.Gamma (ν + n + 1))) *
    (z / 2) ^ (ν + 2 * (n : ℂ))

/-- The quotient `(J_ν(z) cos(νπ) - J_{-ν}(z)) / sin(νπ)` of (3.4). -/
noncomputable def besselYQuot (ν z : ℂ) : ℂ :=
  (besselJC ν z * Complex.cos (ν * Real.pi) - besselJC (-ν) z) / Complex.sin (ν * Real.pi)

open Classical in
/-- **(3.4)**: the Bessel function of the second kind
`Y_ν(z) = (J_ν(z) cos(νπ) - J_{-ν}(z)) / sin(νπ)`, defined for integer `ν`
as the limit `ν → n`. -/
noncomputable def besselYC (ν z : ℂ) : ℂ :=
  if ∃ n : ℤ, (n : ℂ) = ν then Filter.limUnder (nhdsWithin ν {ν}ᶜ) (fun μ => besselYQuot μ z)
  else besselYQuot ν z

/-- The quotient `(π/2) (e^{πiν/2} J_{-ν}(iz) - e^{-πiν/2} J_ν(iz)) / sin(νπ)` of (3.5). -/
noncomputable def besselKQuot (ν z : ℂ) : ℂ :=
  (Real.pi / 2) *
    (Complex.exp (Real.pi * Complex.I * ν / 2) * besselJC (-ν) (Complex.I * z) -
      Complex.exp (-(Real.pi * Complex.I * ν / 2)) * besselJC ν (Complex.I * z)) /
    Complex.sin (ν * Real.pi)

open Classical in
/-- **(3.5)**: the modified Bessel function
`K_ν(z) = (π/2) (e^{πiν/2} J_{-ν}(iz) - e^{-πiν/2} J_ν(iz)) / sin(νπ)`, defined
for integer `ν` as the limit `ν → n`. -/
noncomputable def besselKC (ν z : ℂ) : ℂ :=
  if ∃ n : ℤ, (n : ℂ) = ν then Filter.limUnder (nhdsWithin ν {ν}ᶜ) (fun μ => besselKQuot μ z)
  else besselKQuot ν z

/-- `J_ν(x)` for real order and real argument (the real part of `besselJC`,
which is real for `x > 0`). -/
noncomputable def besselJ (ν x : ℝ) : ℝ := (besselJC (ν : ℂ) (x : ℂ)).re

/-- `Y_ν(x)` for real order and real argument. -/
noncomputable def besselY (ν x : ℝ) : ℝ := (besselYC (ν : ℂ) (x : ℂ)).re

/-- `K_ν(x)` for real order and real argument. -/
noncomputable def besselK (ν x : ℝ) : ℝ := (besselKC (ν : ℂ) (x : ℂ)).re

/-- **(3.7)**: Voronoï's `I_ν(z) = -Y_ν(z) - (2/π) K_ν(z)` (not the modified
Bessel function of the first kind). -/
noncomputable def voronoiI (ν x : ℝ) : ℝ := -besselY ν x - (2 / Real.pi) * besselK ν x

/-- **(2.3)**: `J_ν(x) = (2/(πx))^{1/2} cos(x - νπ/2 - π/4) + O(x^{-3/2})` as
`x → ∞`, for each real `ν`. -/
def besselJ_asymptotic : Prop :=
  ∀ ν : ℝ, ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |besselJ ν x - (2 / (Real.pi * x)) ^ ((1 : ℝ) / 2) *
        Real.cos (x - ν * Real.pi / 2 - Real.pi / 4)| ≤ C * x ^ (-(3 : ℝ) / 2)

/-- **(3.8)**: `Y_ν(x) = (2/(πx))^{1/2} sin(x - νπ/2 - π/4) + O(x^{-3/2})` as
`x → ∞`. -/
def besselY_asymptotic : Prop :=
  ∀ ν : ℝ, ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |besselY ν x - (2 / (Real.pi * x)) ^ ((1 : ℝ) / 2) *
        Real.sin (x - ν * Real.pi / 2 - Real.pi / 4)| ≤ C * x ^ (-(3 : ℝ) / 2)

/-- **(3.9)**: `K_ν(x) = (π/(2x))^{1/2} e^{-x} + O(e^{-x} x^{-3/2})` as `x → ∞`. -/
def besselK_asymptotic : Prop :=
  ∀ ν : ℝ, ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |besselK ν x - (Real.pi / (2 * x)) ^ ((1 : ℝ) / 2) * Real.exp (-x)| ≤
      C * (Real.exp (-x) * x ^ (-(3 : ℝ) / 2))

/-! ### Ordered series and `Ω`-notation -/

/-- The partial sums `∑_{n < N} f n` converge to `L` (ordered, possibly
conditionally convergent, summation). -/
def HasOrderedSum (f : ℕ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, f n) Filter.atTop (nhds L)

/-- `f = Ω(F)`: for some `C > 0`, `|f(x)| > C |F(x)|` for arbitrarily large `x`. -/
def IsOmega (f F : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ᶠ x in atTop, C * |F x| < |f x|

/-- `f = Ω₊(F)`: for some `C > 0`, `f(x) > C |F(x)|` for arbitrarily large `x`. -/
def IsOmegaPlus (f F : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ᶠ x in atTop, C * |F x| < f x

/-- `f = Ω₋(F)`: for some `C > 0`, `f(x) < -C |F(x)|` for arbitrarily large `x`. -/
def IsOmegaMinus (f F : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ᶠ x in atTop, f x < -(C * |F x|)

/-- `f = Ω±(F)`: both `Ω₊` and `Ω₋`. -/
def IsOmegaPM (f F : ℝ → ℝ) : Prop := IsOmegaPlus f F ∧ IsOmegaMinus f F

/-! ### §2, the circle problem -/

/-- **Gauss's inequalities** (proof of Theorem 1): for `x ≥ 2`,
`π(√x - √2)² < R(x) < π(√x + √2)²` for the unweighted count `R(x)`. -/
def gauss_inequalities : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    Real.pi * (Real.sqrt x - Real.sqrt 2) ^ 2 < (latticeCount x : ℝ) ∧
      (latticeCount x : ℝ) < Real.pi * (Real.sqrt x + Real.sqrt 2) ^ 2

/-- **Theorem 1** (Gauss): `P(x) = O(√x)`. -/
def bkz_theorem1_gauss : Prop :=
  circleErrorPrime =O[atTop] fun x : ℝ => Real.sqrt x

/-- **Sierpiński (1906)**: `P(x) = O(x^{1/3})`. -/
def sierpinski_circleBound : Prop :=
  circleErrorPrime =O[atTop] fun x : ℝ => x ^ ((1 : ℝ) / 3)

/-- **Landau (1913)**: `P(x) = O(x^{1/3 + ε})` for every `ε > 0`. -/
def landau_circleBoundEps : Prop :=
  ∀ ε : ℝ, 0 < ε → circleErrorPrime =O[atTop] fun x : ℝ => x ^ ((1 : ℝ) / 3 + ε)

/-- The `n`-th term `r₂(n) (x/n)^{1/2} J₁(2π√(nx))` of the Hardy identity. -/
noncomputable def hardyTerm (x : ℝ) (n : ℕ) : ℝ :=
  (sumTwoSquaresCount n : ℝ) * (x / n) ^ ((1 : ℝ) / 2) *
    besselJ 1 (2 * Real.pi * Real.sqrt ((n : ℝ) * x))

/-- **(2.4)**, the Hardy (Ramanujan–Hardy) identity: for `x > 0`,
`∑'_{0 ≤ n ≤ x} r₂(n) = π x + ∑_{n ≥ 1} r₂(n) (x/n)^{1/2} J₁(2π√(nx))`
(the series converging as an ordered series). -/
def hardy_identity : Prop :=
  ∀ x : ℝ, 0 < x →
    HasOrderedSum (fun n => hardyTerm x (n + 1)) (circleSumPrime x - Real.pi * x)

/-- The Riesz-mean identity (2.5) at a given `ρ` and `x`:
`Γ(ρ+1)⁻¹ ∑_{0 ≤ n ≤ x} r₂(n) (x - n)^ρ
  = π x^{ρ+1} / Γ(ρ+2) + π^{-ρ} ∑_{n ≥ 1} r₂(n) (x/n)^{(ρ+1)/2} J_{ρ+1}(2π√(nx))`. -/
def rieszIdentity (ρ x : ℝ) : Prop :=
  ∃ S : ℝ,
    HasOrderedSum (fun n =>
      (sumTwoSquaresCount (n + 1) : ℝ) * (x / ((n : ℝ) + 1)) ^ ((ρ + 1) / 2) *
        besselJ (ρ + 1) (2 * Real.pi * Real.sqrt (((n : ℝ) + 1) * x))) S ∧
    (1 / Real.Gamma (ρ + 1)) *
        ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (sumTwoSquaresCount n : ℝ) * (x - n) ^ ρ
      = Real.pi * x ^ (ρ + 1) / Real.Gamma (ρ + 2) + Real.pi ^ (-ρ) * S

/-- **(2.5)** (Landau, `ρ = 1`): the Riesz-mean identity holds for `ρ = 1`
and all `x > 0`. -/
def landau_rieszIdentity : Prop :=
  ∀ x : ℝ, 0 < x → rieszIdentity 1 x

/-- **Chandrasekharan–Narasimhan**: (2.5) holds for every `ρ > -1/2` (for
`ρ ≤ 0` at non-integer `x`, where the left side is unambiguous). -/
def chandrasekharanNarasimhan_rieszIdentity : Prop :=
  ∀ ρ x : ℝ, -1 / 2 < ρ → 0 < x → (ρ ≤ 0 → (⌊x⌋₊ : ℝ) ≠ x) → rieszIdentity ρ x

/-- **(2.6)** (Littlewood–Walfisz, Landau): `P(x) = O(x^{37/112 + ε})` for
every `ε > 0`. -/
def bkz_littlewoodWalfisz : Prop :=
  ∀ ε : ℝ, 0 < ε → circleErrorPrime =O[atTop] fun x : ℝ => x ^ ((37 : ℝ) / 112 + ε)

/-! ### §3, the Dirichlet divisor problem -/

/-- **Theorem 2** (Dirichlet), (3.2): `Δ(x) = O(√x)`. -/
def bkz_theorem2_dirichlet : Prop :=
  divisorErrorPrime =O[atTop] fun x : ℝ => Real.sqrt x

/-- The harmonic-sum estimate used in Dirichlet's proof:
`∑_{n ≤ x} 1/n = log x + γ + O(1/x)`. -/
def harmonicSum_estimate : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |(∑ n ∈ upTo x, (1 : ℝ) / n) - (Real.log x + Real.eulerMascheroniConstant)| ≤ C / x

/-- **(3.3)** (Voronoï, 1904): `Δ(x) = O(x^{1/3} log x)`. -/
def voronoi_divisorBound : Prop :=
  divisorErrorPrime =O[atTop] fun x : ℝ => x ^ ((1 : ℝ) / 3) * Real.log x

/-- The `n`-th term `d(n) (x/n)^{1/2} I₁(4π√(nx))` of Voronoï's formula. -/
noncomputable def voronoiTerm (x : ℝ) (n : ℕ) : ℝ :=
  (numDivisors n : ℝ) * (x / n) ^ ((1 : ℝ) / 2) *
    voronoiI 1 (4 * Real.pi * Real.sqrt ((n : ℝ) * x))

/-- **(3.6)**, Voronoï's formula: for `x > 0`,
`∑'_{n ≤ x} d(n) = x (log x + 2γ - 1) + 1/4 + ∑_{n ≥ 1} d(n) (x/n)^{1/2} I₁(4π√(nx))`
(ordered summation). -/
def voronoi_formula : Prop :=
  ∀ x : ℝ, 0 < x → HasOrderedSum (fun n => voronoiTerm x (n + 1)) (divisorErrorPrime x)

/-! ### §4, upper bounds -/

/-- `P(x) = O(x^{a + ε})` and `Δ(x) = O(x^{a + ε})` for every `ε > 0`. -/
def circleDivisorExponent (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (circleErrorPrime =O[atTop] fun x : ℝ => x ^ (a + ε)) ∧
      (divisorErrorPrime =O[atTop] fun x : ℝ => x ^ (a + ε))

/-- Table entry `a = 1/2`: Gauss (≈1800), Dirichlet (1849). -/
def table_gaussDirichlet : Prop := circleDivisorExponent (1 / 2)

/-- Table entry `a = 1/3`: Voronoï (1904), Sierpiński (1906), Landau (1913). -/
def table_voronoiSierpinskiLandau : Prop := circleDivisorExponent (1 / 3)

/-- Table entry `a = 33/100`: van der Corput (1923). -/
def table_vanDerCorput1923 : Prop := circleDivisorExponent (33 / 100)

/-- Table entry `a = 37/112`: Littlewood and Walfisz (1924), Hardy (1925). -/
def table_littlewoodWalfiszHardy : Prop := circleDivisorExponent (37 / 112)

/-- Table entry `a = 163/494`: Walfisz (1927). -/
def table_walfisz1927 : Prop := circleDivisorExponent (163 / 494)

/-- Table entry `a = 27/82`: van der Corput (1928), Nieland (1928). -/
def table_vanDerCorputNieland : Prop := circleDivisorExponent (27 / 82)

/-- Table entry `a = 15/46`: Titchmarsh (1934), Chih (1950), Richert (1953). -/
def table_titchmarshChihRichert : Prop := circleDivisorExponent (15 / 46)

/-- Table entry `a = 13/40`: Hua (1942). -/
def table_hua : Prop := circleDivisorExponent (13 / 40)

/-- Table entry `a = 12/37`: Chen (1963), Kolesnik (1969). -/
def table_chenKolesnik : Prop := circleDivisorExponent (12 / 37)

/-- Table entry `a = 346/1067`: Kolesnik (1973). -/
def table_kolesnik1973 : Prop := circleDivisorExponent (346 / 1067)

/-- Table entry `a = 35/108`: Kolesnik (1982). -/
def table_kolesnik1982 : Prop := circleDivisorExponent (35 / 108)

/-- Table entry `a = 139/429`: Kolesnik (1985). -/
def table_kolesnik1985 : Prop := circleDivisorExponent (139 / 429)

/-- Table entry `a = 7/22`: Iwaniec and Mozzochi (1988). -/
def table_iwaniecMozzochi : Prop := circleDivisorExponent (7 / 22)

/-- Table entry `a = 23/73`: Huxley (1993). -/
def table_huxley1993 : Prop := circleDivisorExponent (23 / 73)

/-- Table entry `a = 131/416`: Huxley (2003). -/
def table_huxley2003 : Prop := circleDivisorExponent (131 / 416)

/-- The height `T = 2π √((N + ½) x)` of (4.1), i.e. `N + ½ = T²/(4π²x)`. -/
noncomputable def titchmarshT (x : ℝ) (N : ℕ) : ℝ :=
  2 * Real.pi * Real.sqrt (((N : ℝ) + 1 / 2) * x)

/-- **(4.1)** (Titchmarsh, (12.4.3)), as printed: for `a > 0`, `c > 1`,
`Δ(x) = x^{1/4}/(π√2) ∑_{n ≤ N} d(n) n^{-3/4} cos(4π√(nx) - π/4)
         + O(x^{-1/4}) + O(T^{2a} x^{-a}) + O(x^c / T)`
where `N + ½ = T²/(4π²x)`. -/
def titchmarsh_truncatedVoronoi : Prop :=
  ∀ a c : ℝ, 0 < a → 1 < c → ∃ C x₀ : ℝ, ∀ (x : ℝ) (N : ℕ), x₀ ≤ x → 1 ≤ N →
    |divisorErrorPrime x -
        x ^ ((1 : ℝ) / 4) / (Real.pi * Real.sqrt 2) *
          ∑ n ∈ Finset.Icc 1 N, (numDivisors n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 4) *
            Real.cos (4 * Real.pi * Real.sqrt ((n : ℝ) * x) - Real.pi / 4)| ≤
      C * (x ^ (-(1 : ℝ) / 4) + titchmarshT x N ^ (2 * a) / x ^ a +
            x ^ c / titchmarshT x N)

/-! ### §5, lower bounds -/

/-- **Landau (1915)**: `P(x) ≠ O(x^{1/4 - ε})` for every `ε > 0`. -/
def landau_noQuarterBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ¬ (circleErrorPrime =O[atTop] fun x : ℝ => x ^ ((1 : ℝ) / 4 - ε))

/-- The smoothed identity used by Landau:
`∑_{0 ≤ n ≤ x} r₂(n) (x - n) = π x²/2 + π⁻¹ ∑_{n ≥ 1} r₂(n) (x/n) J₂(2π√(nx))`
for `x > 0`. -/
def landau_smoothedIdentity : Prop :=
  ∀ x : ℝ, 0 < x → ∃ S : ℝ,
    HasOrderedSum (fun n =>
      (sumTwoSquaresCount (n + 1) : ℝ) * (x / ((n : ℝ) + 1)) *
        besselJ 2 (2 * Real.pi * Real.sqrt (((n : ℝ) + 1) * x))) S ∧
    (∑ n ∈ Finset.range (⌊x⌋₊ + 1), (sumTwoSquaresCount n : ℝ) * (x - n))
      = Real.pi * x ^ 2 / 2 + (1 / Real.pi) * S

/-- **(5.1)** (Hardy, 1915): `P(x) = Ω±(x^{1/4})`. -/
def hardy_omegaPM_circle : Prop :=
  IsOmegaPM circleErrorPrime fun x : ℝ => x ^ ((1 : ℝ) / 4)

/-- **Hardy (1916)**, the analogue of (5.1) for the divisor problem:
`Δ(x) = Ω±(x^{1/4})`. -/
def hardy_omegaPM_divisor : Prop :=
  IsOmegaPM divisorErrorPrime fun x : ℝ => x ^ ((1 : ℝ) / 4)

/-- **(5.2)** (Hardy, 1916): `P(x) = Ω₋((x log x)^{1/4})`. -/
def hardy_omegaMinus_circle : Prop :=
  IsOmegaMinus circleErrorPrime fun x : ℝ => (x * Real.log x) ^ ((1 : ℝ) / 4)

/-- **(5.3)** (Hardy, 1916): `Δ(x) = Ω₊((x log x)^{1/4} log log x)`. -/
def hardy_omegaPlus_divisor : Prop :=
  IsOmegaPlus divisorErrorPrime fun x : ℝ =>
    (x * Real.log x) ^ ((1 : ℝ) / 4) * Real.log (Real.log x)

/-- Gangadharan's bound `x^{1/4} (log log x)^{1/4} (log log log x)^{1/4}`. -/
noncomputable def gangadharanBound (x : ℝ) : ℝ :=
  x ^ ((1 : ℝ) / 4) * Real.log (Real.log x) ^ ((1 : ℝ) / 4) *
    Real.log (Real.log (Real.log x)) ^ ((1 : ℝ) / 4)

/-- **Gangadharan (1961)**: `P(x) = Ω±(x^{1/4} (log log x)^{1/4} (log log log x)^{1/4})`. -/
def gangadharan_omega_circle : Prop := IsOmegaPM circleErrorPrime gangadharanBound

/-- The analogue of Gangadharan's theorem for `Δ(x)`. -/
def gangadharan_omega_divisor : Prop := IsOmegaPM divisorErrorPrime gangadharanBound

/-- The Corrádi–Kátai bound
`x^{1/4} exp(C₁ (log log x)^{1/4} (log log log x)^{-3/4})`. -/
noncomputable def corradiKataiBound (C₁ x : ℝ) : ℝ :=
  x ^ ((1 : ℝ) / 4) *
    Real.exp (C₁ * Real.log (Real.log x) ^ ((1 : ℝ) / 4) *
      Real.log (Real.log (Real.log x)) ^ (-(3 : ℝ) / 4))

/-- **Corrádi–Kátai (1967)**: for some constant `C₁ > 0`,
`P(x) = Ω₊(x^{1/4} exp(C₁ (log log x)^{1/4} (log log log x)^{-3/4}))`. -/
def corradiKatai_omega_circle : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ IsOmegaPlus circleErrorPrime (corradiKataiBound C₁)

/-- The analogue of the Corrádi–Kátai theorem for `Δ(x)`. -/
def corradiKatai_omega_divisor : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ IsOmegaPlus divisorErrorPrime (corradiKataiBound C₁)

/-- Hafner's bound
`x^{1/4} (log x)^{1/4} (log log x)^{(log 2)/4} exp(-C₂ √(log log log x))`. -/
noncomputable def hafnerBound (C₂ x : ℝ) : ℝ :=
  x ^ ((1 : ℝ) / 4) * Real.log x ^ ((1 : ℝ) / 4) *
    Real.log (Real.log x) ^ (Real.log 2 / 4) *
    Real.exp (-C₂ * Real.sqrt (Real.log (Real.log (Real.log x))))

/-- **Hafner (1981)** (and Selberg, unpublished): for some constant `C₂ > 0`,
`P(x) = Ω₋(x^{1/4} (log x)^{1/4} (log log x)^{(log 2)/4} exp(-C₂ √(log log log x)))`. -/
def hafner_omega_circle : Prop :=
  ∃ C₂ : ℝ, 0 < C₂ ∧ IsOmegaMinus circleErrorPrime (hafnerBound C₂)

/-- The analogue of Hafner's theorem for `Δ(x)` (with `Ω₊` in place of `Ω₋`,
matching the sign of Hardy's (5.3); the survey only says "analogous"). -/
def hafner_omega_divisor : Prop :=
  ∃ C₂ : ℝ, 0 < C₂ ∧ IsOmegaPlus divisorErrorPrime (hafnerBound C₂)

/-- Soundararajan's bound
`x^{1/4} (log x)^{1/4} (log log x)^{3(2^{1/3} - 1)/4} / (log log log x)^{5/8}`. -/
noncomputable def soundararajanBound (x : ℝ) : ℝ :=
  x ^ ((1 : ℝ) / 4) * Real.log x ^ ((1 : ℝ) / 4) *
    Real.log (Real.log x) ^ (3 * ((2 : ℝ) ^ ((1 : ℝ) / 3) - 1) / 4) /
    Real.log (Real.log (Real.log x)) ^ ((5 : ℝ) / 8)

/-- **Soundararajan (2003)**: `P(x) = Ω(soundararajanBound x)`. -/
def soundararajan_omega_circle : Prop := IsOmega circleErrorPrime soundararajanBound

/-- The analogue of Soundararajan's theorem for `Δ(x)`. -/
def soundararajan_omega_divisor : Prop := IsOmega divisorErrorPrime soundararajanBound

/-- **(5.4)**, the conjectures: `P(x) = O(x^{1/4 + ε})` and
`Δ(x) = O(x^{1/4 + ε})` for every `ε > 0`. -/
def circleDivisor_conjecture : Prop := circleDivisorExponent (1 / 4)

/-- **The Lindelöf hypothesis**: `ζ(1/2 + it) = O(|t|^ε)` as `|t| → ∞`, for
every `ε > 0`. -/
def lindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ |t| →
    ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ≤ C * |t| ^ ε

/-- **Voronoï's mean value**: `∫₀^X Δ(x) dx = X/4 + O(X^{3/4})`. -/
def voronoi_meanValue : Prop :=
  ∃ C X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    |(∫ x in (0 : ℝ)..X, divisorErrorPrime x) - X / 4| ≤ C * X ^ ((3 : ℝ) / 4)

/-- **Tsang (`m = 3, 4`), Zhai (`5 ≤ m ≤ 9`)**: for `3 ≤ m ≤ 9` there is
`C_m > 0` with `∫₀^X P(x)^m dx ∼ (-1)^m C_m X^{1 + m/4}` as `X → ∞`. -/
def tsangZhai_moments : Prop :=
  ∀ m : ℕ, 3 ≤ m → m ≤ 9 → ∃ C : ℝ, 0 < C ∧
    Filter.Tendsto
      (fun X : ℝ => (∫ x in (0 : ℝ)..X, circleErrorPrime x ^ m) /
        ((-1 : ℝ) ^ m * C * X ^ (1 + (m : ℝ) / 4)))
      Filter.atTop (nhds 1)

/-- **(5.5)** (Ramanujan, in Hardy's paper): for `a, b > 0`,
`∑_{n ≥ 0} r₂(n) (n + a)^{-1/2} e^{-2π√((n + a) b)}
  = ∑_{n ≥ 0} r₂(n) (n + b)^{-1/2} e^{-2π√((n + b) a)}`. -/
def ramanujan_symmetricIdentity : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    (∑' n : ℕ, (sumTwoSquaresCount n : ℝ) / Real.sqrt ((n : ℝ) + a) *
        Real.exp (-2 * Real.pi * Real.sqrt (((n : ℝ) + a) * b))) =
      ∑' n : ℕ, (sumTwoSquaresCount n : ℝ) / Real.sqrt ((n : ℝ) + b) *
        Real.exp (-2 * Real.pi * Real.sqrt (((n : ℝ) + b) * a))

/-- **Hardy's key identity** (from (5.5)): for `ℜ s > 0`,
`∑_{n ≥ 1} r₂(n) e^{-s√n} = 2π/s² - 1 + 2πs ∑_{n ≥ 1} r₂(n) (s² + 4π²n)^{-3/2}`. -/
def hardy_keyIdentity : Prop :=
  ∀ s : ℂ, 0 < s.re →
    (∑' n : ℕ, (sumTwoSquaresCount (n + 1) : ℂ) *
        Complex.exp (-s * ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ))) =
      2 * Real.pi / s ^ 2 - 1 +
        2 * Real.pi * s * ∑' n : ℕ, (sumTwoSquaresCount (n + 1) : ℂ) /
          (s ^ 2 + 4 * (Real.pi : ℂ) ^ 2 * ((n : ℂ) + 1)) ^ ((3 : ℂ) / 2)

/-! ### §6, Ramanujan's page 335 -/

/-- **(6.1)** (Jacobi): `r₂(n) = 4 ∑_{d ∣ n, d odd} (-1)^{(d-1)/2}` for `n ≥ 1`. -/
def jacobi_twoSquaresFormula : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (sumTwoSquaresCount n : ℤ) =
      4 * ∑ d ∈ (Nat.divisors n).filter (fun d => d % 2 = 1), (-1 : ℤ) ^ ((d - 1) / 2)

open Classical in
/-- **(6.3)**: the endpoint-weighted floor `F(x) = ⌊x⌋` for non-integer `x`,
`F(x) = x - ½` for integer `x`. -/
noncomputable def endpointFloor (x : ℝ) : ℝ :=
  if (⌊x⌋ : ℝ) = x then x - 1 / 2 else (⌊x⌋ : ℝ)

/-- **(6.2)**, the elementary identity in the last two lines: for `x > 0`,
`∑'_{0 < n ≤ x} r₂(n) = 4 ∑_{0 < d ≤ x} F(x/d) sin(πd/2)`. -/
def bkz_62 : Prop :=
  ∀ x : ℝ, 0 < x →
    circleSumPrime x - 1 =
      4 * ∑ d ∈ upTo x, endpointFloor (x / d) * Real.sin (Real.pi * d / 2)

/-- The left-hand side `∑_{n ≥ 1} F(x/n) sin(2πnθ)` of (6.4) (a finite sum,
since `F(x/n) = 0` for `n > x`). -/
noncomputable def ramanujanLHS (θ x : ℝ) : ℝ :=
  ∑ n ∈ upTo x, endpointFloor (x / n) * Real.sin (2 * Real.pi * n * θ)

/-- The elementary part `π x (½ - θ) - ¼ cot(πθ)` of the right-hand side of (6.4). -/
noncomputable def ramanujanMain (θ x : ℝ) : ℝ :=
  Real.pi * x * (1 / 2 - θ) - (1 / 4) * (Real.cos (Real.pi * θ) / Real.sin (Real.pi * θ))

/-- The summand
`J₁(4π√(m(n+θ)x)) / √(m(n+θ)) - J₁(4π√(m(n+1-θ)x)) / √(m(n+1-θ))` of (6.4). -/
noncomputable def ramanujanTerm (θ x : ℝ) (m n : ℕ) : ℝ :=
  besselJ 1 (4 * Real.pi * Real.sqrt ((m : ℝ) * ((n : ℝ) + θ) * x)) /
      Real.sqrt ((m : ℝ) * ((n : ℝ) + θ)) -
    besselJ 1 (4 * Real.pi * Real.sqrt ((m : ℝ) * ((n : ℝ) + 1 - θ) * x)) /
      Real.sqrt ((m : ℝ) * ((n : ℝ) + 1 - θ))

/-- The double series of (6.4) summed as Ramanujan wrote it, `m ≥ 1` outside
and `n ≥ 0` inside, has value `S`. -/
def ramanujanDoubleSum_original (θ x S : ℝ) : Prop :=
  ∃ g : ℕ → ℝ, (∀ m : ℕ, HasOrderedSum (fun n => ramanujanTerm θ x (m + 1) n) (g m)) ∧
    HasOrderedSum g S

/-- The double series of (6.4) with the order of summation reversed, `n ≥ 0`
outside and `m ≥ 1` inside, has value `S`. -/
def ramanujanDoubleSum_reversed (θ x S : ℝ) : Prop :=
  ∃ h : ℕ → ℝ, (∀ n : ℕ, HasOrderedSum (fun m => ramanujanTerm θ x (m + 1) n) (h n)) ∧
    HasOrderedSum h S

/-- The double series of (6.4) summed with "the product of the indices tending
to infinity": the sums over `m ≥ 1`, `n ≥ 0` with `m (n + 1) ≤ N` tend to `S`
as `N → ∞`.  (One reading of the survey's description of [5].) -/
def ramanujanDoubleSum_product (θ x S : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => ∑ p ∈ (Finset.Icc 1 N ×ˢ Finset.range N).filter
        (fun p : ℕ × ℕ => p.1 * (p.2 + 1) ≤ N),
      ramanujanTerm θ x p.1 p.2)
    Filter.atTop (nhds S)

/-- **Entry 3** ([33, p. 335]), (6.4), as Ramanujan wrote it (proved in [6]):
for `0 < θ < 1` and `x > 0`,
`∑_{n ≥ 1} F(x/n) sin(2πnθ) = π x (½ - θ) - ¼ cot(πθ)
   + ½ √x ∑_{m ≥ 1} ∑_{n ≥ 0} {J₁(4π√(m(n+θ)x))/√(m(n+θ)) - J₁(4π√(m(n+1-θ)x))/√(m(n+1-θ))}`. -/
def ramanujan_entry3 : Prop :=
  ∀ θ x : ℝ, 0 < θ → θ < 1 → 0 < x → ∃ S : ℝ,
    ramanujanDoubleSum_original θ x S ∧
      ramanujanLHS θ x = ramanujanMain θ x + (1 / 2) * Real.sqrt x * S

/-- **Entry 3 with the order of summation reversed** (Berndt–Zaharescu [8]). -/
def ramanujan_entry3_reversed : Prop :=
  ∀ θ x : ℝ, 0 < θ → θ < 1 → 0 < x → ∃ S : ℝ,
    ramanujanDoubleSum_reversed θ x S ∧
      ramanujanLHS θ x = ramanujanMain θ x + (1 / 2) * Real.sqrt x * S

/-- **Entry 3 with the product of the indices tending to infinity**
(Berndt–Kim–Zaharescu [5]). -/
def ramanujan_entry3_product : Prop :=
  ∀ θ x : ℝ, 0 < θ → θ < 1 → 0 < x → ∃ S : ℝ,
    ramanujanDoubleSum_product θ x S ∧
      ramanujanLHS θ x = ramanujanMain θ x + (1 / 2) * Real.sqrt x * S

/-- The summand
`(n+θ)⁻¹ sin²(π(n+θ)x/m) - (n+1-θ)⁻¹ sin²(π(n+1-θ)x/m)` of (6.5). -/
noncomputable def bzTerm (θ x : ℝ) (n m : ℕ) : ℝ :=
  (1 / ((n : ℝ) + θ)) * Real.sin (Real.pi * ((n : ℝ) + θ) * x / m) ^ 2 -
    (1 / ((n : ℝ) + 1 - θ)) * Real.sin (Real.pi * ((n : ℝ) + 1 - θ) * x / m) ^ 2

/-- **Theorem 4** (Berndt–Zaharescu), (6.5): for `0 < θ < 1` and `x > 0`,
`∑_{n ≥ 1} F(x/n) sin(2πnθ) - π x (½ - θ)
   = π⁻¹ ∑_{n ≥ 0} ∑_{m ≥ 1} {(n+θ)⁻¹ sin²(π(n+θ)x/m) - (n+1-θ)⁻¹ sin²(π(n+1-θ)x/m)}`. -/
def berndtZaharescu_theorem4 : Prop :=
  ∀ θ x : ℝ, 0 < θ → θ < 1 → 0 < x → ∃ S : ℝ,
    (∃ h : ℕ → ℝ, (∀ n : ℕ, HasOrderedSum (fun m => bzTerm θ x n (m + 1)) (h n)) ∧
      HasOrderedSum h S) ∧
    ramanujanLHS θ x - Real.pi * x * (1 / 2 - θ) = (1 / Real.pi) * S

/-- **Corollary 5** (Berndt–Zaharescu), (6.7): for `x > 0`,
`∑'_{0 ≤ n ≤ x} r₂(n) = π x + 2 √x ∑_{n ≥ 0} ∑_{m ≥ 1}
   {J₁(4π√(m(n+¼)x))/√(m(n+¼)) - J₁(4π√(m(n+¾)x))/√(m(n+¾))}`
(`n` outside, `m` inside, as printed). -/
def berndtZaharescu_corollary5 : Prop :=
  ∀ x : ℝ, 0 < x → ∃ S : ℝ,
    ramanujanDoubleSum_reversed (1 / 4) x S ∧
      circleSumPrime x = Real.pi * x + 2 * Real.sqrt x * S

/-- **Berndt–Kim–Zaharescu [5]**: (6.7) also holds when the double series is
summed with the product of the indices tending to infinity (the form in which
it is a rearrangement of the Hardy identity (2.4)). -/
def berndtKimZaharescu_corollary5_product : Prop :=
  ∀ x : ℝ, 0 < x → ∃ S : ℝ,
    ramanujanDoubleSum_product (1 / 4) x S ∧
      circleSumPrime x = Real.pi * x + 2 * Real.sqrt x * S

/-! ### §7, concluding remarks -/

/-- **(7.1)** (Hardy–Littlewood, 1918):
`∫₀^T |ζ(½ + it)|² dt = T log(T/(2π)) + (2γ - 1) T + E(T)` with
`E(T) = o(T log T)`. -/
def hardyLittlewood_meanSquare : Prop :=
  Filter.Tendsto
    (fun T : ℝ =>
      ((∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ^ 2) -
          (T * Real.log (T / (2 * Real.pi)) + (2 * Real.eulerMascheroniConstant - 1) * T)) /
        (T * Real.log T))
    Filter.atTop (nhds 0)

end LeanProofs.IntegerPoints
