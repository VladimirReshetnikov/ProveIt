import IntegerPoints.Basic
import IntegerPoints.ExponentialSums
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Heath-Brown, *The distribution and moments of the error term in the Dirichlet divisor problem*

Formal statements (no proofs) of the results of

> D. R. Heath-Brown, The distribution and moments of the error term in the
> Dirichlet divisor problem, Acta Arith. 60 (1992), 389–415,

transcribed in `Papers/The distribution and moments of the error term in the
Dirichlet divisor problem.tex`.  Every statement is a `Prop`-valued
definition; nothing is asserted.

## Contents

* the error terms `Δ(x)` (`divisorError`), `P(x)` (`circleError`, from
  `IntegerPoints.Basic`), `E(T)` (`zetaMeanError`) and `Δ₃(x)` (`piltz3Error`);
* the notions "limiting distribution with density `f`"
  (`HasLimitingDensity`), "moments converge" (`AbsMomentConverges`,
  `SignedMomentConverges`), the mean value `m_T(f) = T⁻¹ ∫₀ᵀ f`
  (`HasMeanValue`), Hypothesis (H) (`HypothesisH`);
* Theorems 1–6, Lemmas 1–6;
* the truncated Voronoi formulas (5.1) for `Δ(x)` and its §6 analogue for
  `P(x)`, Atkinson's formula for `E(T)` (§6), Atkinson's formula for `Δ₃(x)`
  (§7), the moment bounds (5.3), (7.9) and the pointwise bounds of
  Iwaniec–Mozzochi and Heath-Brown–Huxley quoted in §5–§6;
* the cited background (1.2)–(1.4), Voronoï's `∫₀ˣ Δ = o(X^{5/4})`, Cramér's
  mean square for `P(x)` and Tsang's third and fourth moments;
* the explicit almost-periodic expansions `F(t) = ∑ aₙ(γₙ t)` of §5–§7 and the
  claims that they satisfy Hypothesis (H).

## Conventions

* `d(n)` is `(Nat.divisors n).card` (so `d(0) = 0`), and `d₃(n)` is the
  number of ordered factorisations `n = a b c`.
* The Euler–Mascheroni constant is Mathlib's `Real.eulerMascheroniConstant`.
  The Piltz main term `x P₂(log x)` (the residue of `ζ(s)³ xˢ/s` at `s = 1`)
  involves the first Stieltjes constant `γ₁`, which is not in Mathlib; it is
  defined here (`stieltjesConstant1`) as `lim (∑_{k ≤ n} log k / k − log² n / 2)`.
  The residue formula `P₂(u) = u²/2 + (3γ − 1) u + (3γ² − 3γ − 3γ₁ + 1)` was
  verified symbolically in Wolfram.
* `P(x) = P(x)` of the paper is `circleError x = latticeCount x − π x`, which
  counts the origin (`r(0) = 1`); this differs from `∑_{1 ≤ n ≤ x} r(n) − π x`
  by `1`, which is absorbed by every error term below.
* "Distribution function" (Theorem 1) is rendered for closed intervals
  `I = [a, b]`; since the density is continuous this is equivalent to the
  statement for arbitrary intervals.
* "`X^{-1-k/4} ∫₀ˣ |Δ|ᵏ` converges to a finite limit" is rendered with
  `Filter.Tendsto … (nhds L)`; it is the same as `∫₀ˣ Δ(x)ᵏ dx ∼ C_k X^{1+k/4}`
  when `C_k ≠ 0`.
* `lim_N limsup_T g_N(T) = 0` for the non-negative bounded `g_N` of
  Hypothesis (H) is rendered in the equivalent `ε`–`N₀`–`T₀` form.
* Families `a₁, a₂, …`, `γ₁, γ₂, …` are indexed by `ℕ`; index `0` is unused,
  sums run over `Finset.Icc 1 N`, and infinite sums / linear independence use
  the shifted family `n ↦ aₙ₊₁`.
* `≪` bounds are rendered with explicit constants, quantified after the
  parameters the implied constant may depend on.
* Implicit measurability/integrability assumptions of the paper are made
  explicit where Lean's convention `∫ f = 0` for non-integrable `f` would
  otherwise trivialise a hypothesis.
* In §5–§7 the paper's `aₙ` vanish identically for non-square-free
  (resp. non-cube-free) `n`, and the `γₙ` indexed by *all* `n` are not
  `ℚ`-linearly independent (`γ₄ = 2γ₁`; `∛8 = 2∛1`), so (4.4) and the
  independence hypothesis of Theorem 5 fail for the family as printed.
  Theorem 5 is applied to the subfamily indexed by square-free (cube-free)
  `n`, enumerated in increasing order by `reindex` (`Nat.nth`); the sums
  `∑_{n ≤ N} aₙ(γₙ t)` of (5.2), (6.1), §7 are left over all `n`, as in the
  paper (the discarded terms are zero).
-/

open scoped BigOperators FourierTransform
open Real Finset Filter

namespace LeanProofs.IntegerPoints

/-! ### The error terms -/

/-- `d(n)`: the number of divisors of `n` (`d(0) = 0`). -/
def divisorCount (n : ℕ) : ℕ := (Nat.divisors n).card

/-- `∑_{n ≤ x} d(n)`. -/
noncomputable def divisorSum (x : ℝ) : ℝ := ∑ n ∈ upTo x, (divisorCount n : ℝ)

/-- `Δ(x) = ∑_{n ≤ x} d(n) − x (log x + 2γ − 1)`: the error term of the
Dirichlet divisor problem. -/
noncomputable def divisorError (x : ℝ) : ℝ :=
  divisorSum x - x * (Real.log x + 2 * Real.eulerMascheroniConstant - 1)

/-- `d₃(n)`: the number of ordered triples `(a, b, c)` with `a b c = n`. -/
def piltz3 (n : ℕ) : ℕ := ∑ d ∈ Nat.divisors n, divisorCount (n / d)

/-- The first Stieltjes constant
`γ₁ = lim_{n → ∞} (∑_{k ≤ n} (log k) / k − (log n)² / 2)`. -/
noncomputable def stieltjesConstant1 : ℝ :=
  Filter.limUnder Filter.atTop
    (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, Real.log k / (k : ℝ)) - Real.log n ^ 2 / 2)

/-- The Piltz main term `x P₂(log x) = Res_{s=1} ζ(s)³ xˢ / s`, with
`P₂(u) = u²/2 + (3γ − 1) u + (3γ² − 3γ − 3γ₁ + 1)`. -/
noncomputable def piltz3MainTerm (x : ℝ) : ℝ :=
  x * (Real.log x ^ 2 / 2 + (3 * Real.eulerMascheroniConstant - 1) * Real.log x +
    (3 * Real.eulerMascheroniConstant ^ 2 - 3 * Real.eulerMascheroniConstant -
      3 * stieltjesConstant1 + 1))

/-- `Δ₃(x) = ∑_{n ≤ x} d₃(n) − x P₂(log x)`: the error term of the Piltz
divisor problem for `d₃`. -/
noncomputable def piltz3Error (x : ℝ) : ℝ :=
  (∑ n ∈ upTo x, (piltz3 n : ℝ)) - piltz3MainTerm x

/-- `E(T) = ∫₀ᵀ |ζ(1/2 + i t)|² dt − T (log (T / 2π) + 2γ − 1)`: the error term
of the mean value of the Riemann zeta-function. -/
noncomputable def zetaMeanError (T : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..T, ‖riemannZeta ((1 : ℂ) / 2 + Complex.I * (t : ℂ))‖ ^ 2) -
    T * (Real.log (T / (2 * Real.pi)) + 2 * Real.eulerMascheroniConstant - 1)

/-- `x ↦ x^{-θ} G(x)`: the normalised error term. -/
noncomputable def normalise (θ : ℝ) (G : ℝ → ℝ) (x : ℝ) : ℝ := x ^ (-θ) * G x

/-! ### Distributions, moments and mean values -/

/-- `G` has the limiting distribution with density `f`: for every interval
`I = [a, b]`, `X⁻¹ mes {x ∈ [1, X] : G(x) ∈ I} → ∫_I f(α) dα` as `X → ∞`. -/
def HasLimitingDensity (G f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, a ≤ b →
    Filter.Tendsto
      (fun X : ℝ =>
        (MeasureTheory.volume {x ∈ Set.Icc (1 : ℝ) X | G x ∈ Set.Icc a b}).toReal / X)
      Filter.atTop (nhds (∫ α in a..b, f α))

/-- `f` is smooth and `f⁽ᵏ⁾(α) ≪_{A,k} (1 + |α|)^{-A}` for every `k ≥ 0` and
every `A`. -/
def RapidlyDecayingDerivatives (f : ℝ → ℝ) : Prop :=
  (∀ k : ℕ, ContDiff ℝ k f) ∧
    ∀ (A : ℝ) (k : ℕ), ∃ C : ℝ, ∀ α : ℝ, |iteratedDeriv k f α| ≤ C * (1 + |α|) ^ (-A)

/-- `f` extends to an entire function on `ℂ`. -/
def ExtendsToEntire (f : ℝ → ℝ) : Prop :=
  ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ α : ℝ, g (α : ℂ) = (f α : ℂ)

/-- The conclusion of Theorem 1 for a function `G`: `G` has a distribution
function `f` which, together with all its derivatives, decays faster than any
power, and which extends to an entire function. -/
def DistributionTheoremConclusion (G : ℝ → ℝ) : Prop :=
  ∃ f : ℝ → ℝ, HasLimitingDensity G f ∧ RapidlyDecayingDerivatives f ∧ ExtendsToEntire f

/-- `X^{-1-kθ} ∫₀ˣ |G(x)|ᵏ dx` converges to a finite limit as `X → ∞`
(`k` a real exponent). -/
def AbsMomentConverges (θ k : ℝ) (G : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto
    (fun X : ℝ => X ^ (-(1 + k * θ)) * ∫ x in (0 : ℝ)..X, |G x| ^ k)
    Filter.atTop (nhds L)

/-- `X^{-1-kθ} ∫₀ˣ G(x)ᵏ dx` converges to a finite limit as `X → ∞`
(`k` a natural exponent). -/
def SignedMomentConverges (θ : ℝ) (k : ℕ) (G : ℝ → ℝ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto
    (fun X : ℝ => X ^ (-(1 + (k : ℝ) * θ)) * ∫ x in (0 : ℝ)..X, G x ^ k)
    Filter.atTop (nhds L)

/-- `m_T(g) = T⁻¹ ∫₀ᵀ g(t) dt → L` as `T → ∞` (complex-valued `g`). -/
def HasMeanValue (g : ℝ → ℂ) (L : ℂ) : Prop :=
  Filter.Tendsto (fun T : ℝ => (1 / (T : ℂ)) * ∫ t in (0 : ℝ)..T, g t) Filter.atTop (nhds L)

/-- `m_T(g) = T⁻¹ ∫₀ᵀ g(t) dt → L` as `T → ∞` (real-valued `g`). -/
def HasMeanValueR (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, g t) Filter.atTop (nhds L)

/-! ### Hypothesis (H) and the test functions of Theorem 4 -/

/-- `S_N(t) = ∑_{n ≤ N} aₙ(γₙ t)`. -/
noncomputable def oscSum (a : ℕ → ℝ → ℝ) (γ : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, a n (γ n * t)

/-- Reindex a family `b` (index `0` unused) along the increasing enumeration
`q₁ < q₂ < ⋯` of the positive integers satisfying `p`: `reindex p b k = b (q_k)`
for `k ≥ 1` (`Nat.nth p 0 = q₁` is the least such integer; `p 0` is false for
the predicates used here). -/
noncomputable def reindex {α : Type*} (p : ℕ → Prop) (b : ℕ → α) (k : ℕ) : α :=
  b (Nat.nth p (k - 1))

/-- **Hypothesis (H)**: `aₙ` are continuous real-valued functions of period
`1`, `γₙ ≠ 0`, `F` is measurable, and
`lim_{N → ∞} limsup_{T → ∞} T⁻¹ ∫₀ᵀ min {1, |F(t) − ∑_{n ≤ N} aₙ(γₙ t)|} dt = 0`
(rendered in the equivalent `ε`-`N₀`-`T₀` form). -/
def HypothesisH (F : ℝ → ℝ) (a : ℕ → ℝ → ℝ) (γ : ℕ → ℝ) : Prop :=
  Measurable F ∧
  (∀ n : ℕ, 1 ≤ n → Continuous (a n) ∧ Function.Periodic (a n) 1) ∧
  (∀ n : ℕ, 1 ≤ n → γ n ≠ 0) ∧
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (1 / T) * (∫ t in (0 : ℝ)..T, min 1 (|F t - oscSum a γ N t|)) < ε

/-- A test function of Theorem 4: `p` is continuous, piecewise differentiable
(differentiable away from a set with finitely many points in every bounded
interval), and both `p` and its Fourier transform `p̂` are integrable. -/
def AdmissibleTest (p : ℝ → ℝ) : Prop :=
  Continuous p ∧
  (∃ S : Set ℝ, (∀ R : ℝ, (S ∩ Set.Icc (-R) R).Finite) ∧ ∀ x : ℝ, x ∉ S → DifferentiableAt ℝ p x) ∧
  MeasureTheory.Integrable p MeasureTheory.volume ∧
  MeasureTheory.Integrable (𝓕 (fun x : ℝ => (p x : ℂ))) MeasureTheory.volume

/-- `F` "has a distribution in the sense of Theorem 4": `F` is measurable and
`m_T(p(F))` converges for every admissible test function `p`. -/
def HasWeakDistribution (F : ℝ → ℝ) : Prop :=
  Measurable F ∧ ∀ p : ℝ → ℝ, AdmissibleTest p → ∃ L : ℝ, HasMeanValueR (fun t => p (F t)) L

/-! ### The main theorems, §1 -/

/-- **Heath-Brown, Theorem 1**: `x^{-1/4} Δ(x)` has a distribution function
`f(α)` with `f⁽ᵏ⁾(α) ≪_{A,k} (1 + |α|)^{-A}`, and `f` extends to an entire
function. -/
def heathBrown_theorem1 : Prop :=
  DistributionTheoremConclusion (normalise ((1 : ℝ) / 4) divisorError)

/-- **Heath-Brown, Theorem 2**: for every real `k ∈ [0, 9]`,
`X^{-1-k/4} ∫₀ˣ |Δ(x)|ᵏ dx` converges to a finite limit, and so does the odd
moment `X^{-1-k/4} ∫₀ˣ Δ(x)ᵏ dx` (1.1) for `k = 1, 3, 5, 7, 9`. -/
def heathBrown_theorem2 : Prop :=
  (∀ k : ℝ, 0 ≤ k → k ≤ 9 → AbsMomentConverges ((1 : ℝ) / 4) k divisorError) ∧
  (∀ k : ℕ, Odd k → k ≤ 9 → SignedMomentConverges ((1 : ℝ) / 4) k divisorError)

/-- **Heath-Brown, Theorem 3** for `P(x)`: Theorems 1 and 2 hold verbatim
with `Δ(x)` replaced by the circle-problem error term `P(x)`. -/
def heathBrown_theorem3_circle : Prop :=
  DistributionTheoremConclusion (normalise ((1 : ℝ) / 4) circleError) ∧
  (∀ k : ℝ, 0 ≤ k → k ≤ 9 → AbsMomentConverges ((1 : ℝ) / 4) k circleError) ∧
  (∀ k : ℕ, Odd k → k ≤ 9 → SignedMomentConverges ((1 : ℝ) / 4) k circleError)

/-- **Heath-Brown, Theorem 3** for `E(T)`: Theorems 1 and 2 hold verbatim with
`Δ(x)` replaced by `E(T)`. -/
def heathBrown_theorem3_zetaMean : Prop :=
  DistributionTheoremConclusion (normalise ((1 : ℝ) / 4) zetaMeanError) ∧
  (∀ k : ℝ, 0 ≤ k → k ≤ 9 → AbsMomentConverges ((1 : ℝ) / 4) k zetaMeanError) ∧
  (∀ k : ℕ, Odd k → k ≤ 9 → SignedMomentConverges ((1 : ℝ) / 4) k zetaMeanError)

/-- **Heath-Brown, Theorem 3** for `Δ₃(x)`: Theorem 1 holds for
`x^{-1/3} Δ₃(x)`, and Theorem 2 holds with `X^{-1-k/3}` for real `k ∈ [0, 3)`
and for the odd moment `k = 1` only. -/
def heathBrown_theorem3_piltz3 : Prop :=
  DistributionTheoremConclusion (normalise ((1 : ℝ) / 3) piltz3Error) ∧
  (∀ k : ℝ, 0 ≤ k → k < 3 → AbsMomentConverges ((1 : ℝ) / 3) k piltz3Error) ∧
  SignedMomentConverges ((1 : ℝ) / 3) 1 piltz3Error

/-- **Heath-Brown, Theorem 4**: if `F` satisfies (H), then `m_T(p(F))`
converges as `T → ∞` for every admissible test function `p`. -/
def heathBrown_theorem4 : Prop :=
  ∀ (F : ℝ → ℝ) (a : ℕ → ℝ → ℝ) (γ : ℕ → ℝ), HypothesisH F a γ → HasWeakDistribution F

/-- The extra hypotheses (4.1)–(4.4) of Theorem 5 / Lemma 3 on the functions
`aₙ`, with exponent `μ > 1`: `∫₀¹ aₙ = 0`, `∑ₙ ∫₀¹ aₙ² < ∞`,
`max_{[0,1]} |aₙ| ≪ n^{1-μ}` and `n^μ ∫₀¹ aₙ² → ∞`. -/
def Theorem5Hypotheses (a : ℕ → ℝ → ℝ) (μ : ℝ) : Prop :=
  1 < μ ∧
  (∀ n : ℕ, 1 ≤ n → ∫ t in (0 : ℝ)..1, a n t = 0) ∧
  Summable (fun n : ℕ => ∫ t in (0 : ℝ)..1, a (n + 1) t ^ 2) ∧
  (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, |a n t| ≤ C * (n : ℝ) ^ (1 - μ)) ∧
  Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ μ * ∫ t in (0 : ℝ)..1, a n t ^ 2)
    Filter.atTop Filter.atTop

/-- **Heath-Brown, Theorem 5**: if `F` satisfies (H), the `γₙ` are linearly
independent over `ℚ`, and (4.1)–(4.4) hold for some `μ > 1`, then `F` has a
distribution function with the properties described in Theorem 1. -/
def heathBrown_theorem5 : Prop :=
  ∀ (F : ℝ → ℝ) (a : ℕ → ℝ → ℝ) (γ : ℕ → ℝ) (μ : ℝ),
    HypothesisH F a γ → LinearIndependent ℚ (fun n : ℕ => γ (n + 1)) →
    Theorem5Hypotheses a μ → DistributionTheoremConclusion F

/-- **Heath-Brown, Theorem 6**: if `F` has a distribution in the sense of
Theorem 4 and `∫₀ᵀ |F(t)|ᴷ dt ≪ T` for some `K > 0`, then `m_T(|F|ᵏ)`
converges for every real `k ∈ [0, K)` and `m_T(Fᵏ)` converges for every odd
integer `k < K`. -/
def heathBrown_theorem6 : Prop :=
  ∀ (F : ℝ → ℝ) (K : ℝ), 0 < K → HasWeakDistribution F →
    (∀ T : ℝ, IntervalIntegrable (fun t => |F t| ^ K) MeasureTheory.volume 0 T) →
    (∃ C : ℝ, ∀ T : ℝ, 0 < T → ∫ t in (0 : ℝ)..T, |F t| ^ K ≤ C * T) →
    (∀ k : ℝ, 0 ≤ k → k < K → ∃ L : ℝ, HasMeanValueR (fun t => |F t| ^ k) L) ∧
    (∀ k : ℕ, Odd k → (k : ℝ) < K → ∃ L : ℝ, HasMeanValueR (fun t => F t ^ k) L)

/-! ### §2: Lemmas 1 and 2 -/

/-- `b : ℝ → ℂ` is continuous of period `1`. -/
def PeriodicContinuous (b : ℝ → ℂ) : Prop := Continuous b ∧ Function.Periodic b 1

/-- **Heath-Brown, Lemma 1**: for continuous `bᵢ` of period `1` and real
`γ, γ₁, …, γ_k`, `m_T(e(γ t) b₁(γ₁ t) ⋯ b_k(γ_k t))` converges; if `γ` is
not an integral linear combination of the `γᵢ`, the limit is `0`. -/
def heathBrown_lemma1 : Prop :=
  ∀ (k : ℕ) (b : Fin k → ℝ → ℂ) (γ : ℝ) (γs : Fin k → ℝ),
    (∀ i, PeriodicContinuous (b i)) →
    ∃ L : ℂ, HasMeanValue (fun t : ℝ => e (γ * t) * ∏ i, b i (γs i * t)) L ∧
      ((∀ c : Fin k → ℤ, γ ≠ ∑ i, (c i : ℝ) * γs i) → L = 0)

/-- **Heath-Brown, Lemma 2**: for continuous `bᵢ` of period `1` and real
`γ₁, …, γ_k`, `m_T(b₁(γ₁ t) ⋯ b_k(γ_k t))` converges; if the `γᵢ` are
linearly independent over `ℚ`, the limit is `∏ᵢ ℒ(bᵢ) = ∏ᵢ ∫₀¹ bᵢ`. -/
def heathBrown_lemma2 : Prop :=
  ∀ (k : ℕ) (b : Fin k → ℝ → ℂ) (γs : Fin k → ℝ),
    (∀ i, PeriodicContinuous (b i)) →
    ∃ L : ℂ, HasMeanValue (fun t : ℝ => ∏ i, b i (γs i * t)) L ∧
      (LinearIndependent ℚ γs → L = ∏ i, ∫ t in (0 : ℝ)..1, b i t)

/-! ### §4: Lemma 3 and the characteristic functions `χₙ`, `χ` -/

/-- `χₙ(z) = ∫₀¹ e(z aₙ(t)) dt` (3.4), for complex `z`. -/
noncomputable def charFn (a : ℕ → ℝ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * z * (a n t : ℂ))

/-- `χ(z) = ∏_{n ≥ 1} χₙ(z)` (4.5). -/
noncomputable def charProd (a : ℕ → ℝ → ℝ) (z : ℂ) : ℂ := ∏' n : ℕ, charFn a (n + 1) z

open Classical in
/-- The region `K = {x + i y : |y| ≤ min (1, |x|^{-1/(μ-1)})}` of Lemma 3
(with `min (1, +∞) = 1` on the imaginary axis). -/
noncomputable def lemma3Region (μ : ℝ) : Set ℂ :=
  {z : ℂ | |z.im| ≤ (if z.re = 0 then 1 else min 1 (|z.re| ^ (-(1 : ℝ) / (μ - 1))))}

/-- **Heath-Brown, Lemma 3**: under (4.1)–(4.4) with `μ > 1`, the product
(4.5) converges absolutely, and uniformly on compact subsets of `K`; `χ` is
holomorphic on `K`; `χ(z) ≪_A e^{-A|z|}` on `K` (4.6); and
`(d/dx)ᵏ χ(x) ≪_{A,k} e^{-A|x|}` on the real axis. -/
def heathBrown_lemma3 : Prop :=
  ∀ (a : ℕ → ℝ → ℝ) (μ : ℝ),
    (∀ n : ℕ, 1 ≤ n → Continuous (a n) ∧ Function.Periodic (a n) 1) →
    Theorem5Hypotheses a μ →
    (∀ z ∈ lemma3Region μ, Summable (fun n : ℕ => ‖charFn a (n + 1) z - 1‖)) ∧
    (∀ K₀ : Set ℂ, K₀ ⊆ lemma3Region μ → IsCompact K₀ →
      TendstoUniformlyOn
        (fun (N : ℕ) (z : ℂ) => ∏ n ∈ Finset.range N, charFn a (n + 1) z)
        (charProd a) Filter.atTop K₀) ∧
    DifferentiableOn ℂ (charProd a) (interior (lemma3Region μ)) ∧
    (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ z ∈ lemma3Region μ,
      ‖charProd a z‖ ≤ C * Real.exp (-A * ‖z‖)) ∧
    (∀ (A : ℝ) (k : ℕ), 0 < A → ∃ C : ℝ, ∀ x : ℝ,
      ‖iteratedDeriv k (fun x : ℝ => charProd a (x : ℂ)) x‖ ≤ C * Real.exp (-A * |x|))

/-- **§4, conclusion of the proof of Theorem 5**: the density is
`f = χ̂`, the Fourier transform of `χ` restricted to the real axis (which is
real and non-negative). -/
def heathBrown_theorem5_density : Prop :=
  ∀ (F : ℝ → ℝ) (a : ℕ → ℝ → ℝ) (γ : ℕ → ℝ) (μ : ℝ),
    HypothesisH F a γ → LinearIndependent ℚ (fun n : ℕ => γ (n + 1)) →
    Theorem5Hypotheses a μ →
    (∀ α : ℝ, (𝓕 (fun x : ℝ => charProd a (x : ℂ)) α).im = 0 ∧
      0 ≤ (𝓕 (fun x : ℝ => charProd a (x : ℂ)) α).re) ∧
    HasLimitingDensity F (fun α : ℝ => (𝓕 (fun x : ℝ => charProd a (x : ℂ)) α).re)

/-! ### §5: the divisor problem -/

/-- The truncated Voronoï sum
`(x^{1/4} / (π √2)) ∑_{n ≤ X} d(n) n^{-3/4} cos (4π √(n x) − π/4)`. -/
noncomputable def voronoiDivisorSum (X x : ℝ) : ℝ :=
  x ^ ((1 : ℝ) / 4) / (Real.pi * Real.sqrt 2) *
    ∑ n ∈ upTo X, (divisorCount n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 4) *
      Real.cos (4 * Real.pi * Real.sqrt (n * x) - Real.pi / 4)

/-- **Heath-Brown, (5.1)** (truncated Voronoï formula, Titchmarsh (12.4.4)):
for any fixed `ε > 0`, uniformly for `X ≤ x ≤ 4X`,
`Δ(x) = (x^{1/4} / (π √2)) ∑_{n ≤ X} d(n) n^{-3/4} cos (4π √(n x) − π/4) + O(X^ε)`. -/
def heathBrown_truncatedVoronoi_divisor : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X x : ℝ, 1 ≤ X → X ≤ x → x ≤ 4 * X →
    |divisorError x - voronoiDivisorSum X x| ≤ C * X ^ ε

/-- The standard truncated Voronoï formula with a free truncation parameter
(Titchmarsh §12.4, Ivić Ch. 3), from which (5.1) follows by taking `N = X`:
for `1 ≤ N ≤ x`,
`Δ(x) = (x^{1/4} / (π √2)) ∑_{n ≤ N} d(n) n^{-3/4} cos (4π √(n x) − π/4)
        + O(x^{1/2+ε} N^{-1/2})`.
This is not a numbered result of the paper; it is recorded here because the
project relies on it. -/
def truncatedVoronoi_divisor_general : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x N : ℝ, 1 ≤ N → N ≤ x →
    |divisorError x - voronoiDivisorSum N x| ≤ C * x ^ ((1 : ℝ) / 2 + ε) / N ^ ((1 : ℝ) / 2)

/-- `F(t) = t^{-1/2} Δ(t²)` of §5. -/
noncomputable def divisorF (t : ℝ) : ℝ := t ^ (-(1 : ℝ) / 2) * divisorError (t ^ 2)

open Classical in
/-- The almost-periodic coefficients of §5:
`aₙ(t) = (μ²(n) / n^{3/4}) (π √2)⁻¹ ∑_{r ≥ 1} d(n r²) r^{-3/2} cos (2π r t − π/4)`. -/
noncomputable def divisorOscCoeff (n : ℕ) (t : ℝ) : ℝ :=
  (if Squarefree n then 1 else 0) / (n : ℝ) ^ ((3 : ℝ) / 4) / (Real.pi * Real.sqrt 2) *
    ∑' r : ℕ, (divisorCount (n * (r + 1) ^ 2) : ℝ) / ((r + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) *
      Real.cos (2 * Real.pi * ((r + 1 : ℕ) : ℝ) * t - Real.pi / 4)

/-- `γₙ = 2 √n` of §5. -/
noncomputable def divisorGamma (n : ℕ) : ℝ := 2 * Real.sqrt n

/-- **§5, (5.2)**: for `1 ≤ N ≤ T^{1/2}`,
`∫_T^{2T} |F(t) − ∑_{n ≤ N} aₙ(γₙ t)|² dt ≪_ε T N^{ε − 1/2}`. -/
def heathBrown_divisorMeanSquareApprox : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), 1 ≤ T → 1 ≤ N → (N : ℝ) ≤ T ^ ((1 : ℝ) / 2) →
    ∫ t in T..(2 * T), (divisorF t - oscSum divisorOscCoeff divisorGamma N t) ^ 2 ≤
      C * T * (N : ℝ) ^ (ε - 1 / 2)

/-- **§5**: `F(t) = t^{-1/2} Δ(t²)` satisfies Hypothesis (H) with the `aₙ`,
`γₙ` above, and the hypotheses of Theorem 5 with `μ = 5/3` hold for the
subfamily indexed by square-free `n` (the only one for which they can hold:
`aₙ ≡ 0` and `γₙ ∈ ℚ γ_{n'}` for non-square-free `n`). -/
def heathBrown_divisorHypothesisH : Prop :=
  HypothesisH divisorF (reindex Squarefree divisorOscCoeff) (reindex Squarefree divisorGamma) ∧
    LinearIndependent ℚ (fun n : ℕ => reindex Squarefree divisorGamma (n + 1)) ∧
    Theorem5Hypotheses (reindex Squarefree divisorOscCoeff) ((5 : ℝ) / 3)

/-- **(5.3)** with exponent `K`: `∫₀ˣ |Δ(x)|ᴷ dx ≪_ε X^{1 + K/4 + ε}`. -/
def divisorMomentBound (K : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
    ∫ x in (0 : ℝ)..X, |divisorError x| ^ K ≤ C * X ^ (1 + K / 4 + ε)

/-- **Ivić, Theorem 13.9** (quoted in §5): (5.3) holds with `K = 35/4`. -/
def ivic_divisorMomentBound : Prop := divisorMomentBound ((35 : ℝ) / 4)

/-- **Iwaniec–Mozzochi** (quoted in §5): `Δ(x) ≪_ε x^{7/22 + ε}`. -/
def iwaniecMozzochi_divisorBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |divisorError x| ≤ C * x ^ ((7 : ℝ) / 22 + ε)

/-- **§5**: injecting Iwaniec–Mozzochi into Ivić's argument, (5.3) holds with
`K = 28/3`. -/
def heathBrown_divisorMomentBound : Prop := divisorMomentBound ((28 : ℝ) / 3)

/-- **Heath-Brown, Lemma 4**: if (5.3) holds for some `K > 2`, then
`∫₀ˣ |Δ(x)|ᵏ dx ≪ X^{1 + k/4}` for every `0 < k < K`. -/
def heathBrown_lemma4 : Prop :=
  ∀ K : ℝ, 2 < K → divisorMomentBound K →
    ∀ k : ℝ, 0 < k → k < K → ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
      ∫ x in (0 : ℝ)..X, |divisorError x| ^ k ≤ C * X ^ (1 + k / 4)

/-- **§5, proof of Lemma 4**: the sharper statement actually proved,
`∫_T^{2T} |F(t)|ᵏ dt ≪ T` for `F(t) = t^{-1/2} Δ(t²)`. -/
def heathBrown_lemma4_dyadic : Prop :=
  ∀ K : ℝ, 2 < K → divisorMomentBound K →
    ∀ k : ℝ, 0 < k → k < K → ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫ t in T..(2 * T), |divisorF t| ^ k ≤ C * T

/-- `n` is square-full: every prime factor of `n` divides it at least twice. -/
def Squarefull (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- **Heath-Brown, Lemma 5**: for positive integers `n₁, …, n_{2L} ≤ N⁴`,
`|√n₁ ± ⋯ ± √n_{2L}| ≫_L N^{-2^{2L+1}}` unless the product `n₁ ⋯ n_{2L}` is
square-full. -/
def heathBrown_lemma5 : Prop :=
  ∀ L : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ (N : ℕ) (n : Fin (2 * L) → ℕ) (σ : Fin (2 * L) → ℤ),
      1 ≤ N → (∀ i, 1 ≤ n i ∧ n i ≤ N ^ 4) → (∀ i, σ i = 1 ∨ σ i = -1) →
      ¬ Squarefull (∏ i, n i) →
      c * (N : ℝ) ^ (-((2 : ℝ) ^ (2 * L + 1))) ≤ |∑ i, (σ i : ℝ) * Real.sqrt (n i)|

/-! ### §6: the circle problem and `E(T)` -/

/-- The truncated Voronoï sum for the circle problem,
`−(x^{1/4} / π) ∑_{n ≤ X} r(n) n^{-3/4} cos (2π √(n x) + π/4)`. -/
noncomputable def voronoiCircleSum (X x : ℝ) : ℝ :=
  -(x ^ ((1 : ℝ) / 4) / Real.pi) *
    ∑ n ∈ upTo X, (sumTwoSquaresCount n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 4) *
      Real.cos (2 * Real.pi * Real.sqrt (n * x) + Real.pi / 4)

/-- **Heath-Brown, §6** (truncated Voronoï formula for `P(x)`, proved by the
method of Titchmarsh §12.4 applied to `∑ r(n) n^{-s}`): for any fixed `ε > 0`,
uniformly for `X ≤ x ≤ 4X`,
`P(x) = −(x^{1/4} / π) ∑_{n ≤ X} r(n) n^{-3/4} cos (2π √(n x) + π/4) + O(X^ε)`. -/
def heathBrown_truncatedVoronoi_circle : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X x : ℝ, 1 ≤ X → X ≤ x → x ≤ 4 * X →
    |circleError x - voronoiCircleSum X x| ≤ C * X ^ ε

/-- The standard truncated Voronoï formula for `P(x)` with a free truncation
parameter (Ivić Ch. 13), from which the §6 formula follows with `N = X`: for
`1 ≤ N ≤ x`,
`P(x) = −(x^{1/4} / π) ∑_{n ≤ N} r(n) n^{-3/4} cos (2π √(n x) + π/4)
        + O(x^{1/2+ε} N^{-1/2})`.
Not a numbered result of the paper; recorded because the project relies on it. -/
def truncatedVoronoi_circle_general : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x N : ℝ, 1 ≤ N → N ≤ x →
    |circleError x - voronoiCircleSum N x| ≤ C * x ^ ((1 : ℝ) / 2 + ε) / N ^ ((1 : ℝ) / 2)

/-- **(5.3) for `P(x)`** with exponent `K`: `∫₀ˣ |P(x)|ᴷ dx ≪_ε X^{1 + K/4 + ε}`. -/
def circleMomentBound (K : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
    ∫ x in (0 : ℝ)..X, |circleError x| ^ K ≤ C * X ^ (1 + K / 4 + ε)

/-- **Iwaniec–Mozzochi** (quoted in §6): `P(x) ≪_ε x^{7/22 + ε}`. -/
def iwaniecMozzochi_circleBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |circleError x| ≤ C * x ^ ((7 : ℝ) / 22 + ε)

/-- **§6**: the moment bound for `P(x)` holds with `K = 28/3` (Ivić, Theorem
13.2, with the Iwaniec–Mozzochi bound inserted). -/
def heathBrown_circleMomentBound : Prop := circleMomentBound ((28 : ℝ) / 3)

/-- `f(n, T) = 2T arsinh √(πn/(2T)) + √(π² n² + 2π n T) − π/4` of Atkinson's
formula. -/
noncomputable def atkinsonPhase (n : ℕ) (T : ℝ) : ℝ :=
  2 * T * Real.arsinh (Real.sqrt (Real.pi * n / (2 * T))) +
    Real.sqrt (Real.pi ^ 2 * (n : ℝ) ^ 2 + 2 * Real.pi * n * T) - Real.pi / 4

/-- `Aₙ(T) = 2^{-1/2} (−1)ⁿ d(n) (nT/(2π) + n²/4)^{-1/4} (arsinh √(πn/(2T)))⁻¹ cos f(n, T)`. -/
noncomputable def atkinsonTerm (n : ℕ) (T : ℝ) : ℝ :=
  (1 / Real.sqrt 2) * (-1 : ℝ) ^ n * (divisorCount n : ℝ) *
    (n * T / (2 * Real.pi) + (n : ℝ) ^ 2 / 4) ^ (-(1 : ℝ) / 4) *
    (Real.arsinh (Real.sqrt (Real.pi * n / (2 * T))))⁻¹ * Real.cos (atkinsonPhase n T)

/-- **Atkinson's formula** as used in §6 (with Heath-Brown [4, Lemma 3]):
uniformly for `X ≤ t ≤ 4X`, `E(t) = ∑_{n ≤ X} Aₙ(t) + Σ₂(t) + O(log² t)`, where
`∫_X^{4X} Σ₂(t)² dt ≪ X (log X)⁴`.  `Σ₂` is required to be measurable: without
this, a non-measurable `Σ₂` makes `∫ Σ₂² = 0` in Lean and the statement is
trivially satisfiable. -/
def atkinson_formula : Prop :=
  ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → ∃ S₂ : ℝ → ℝ, Measurable S₂ ∧
    (∫ t in X..(4 * X), S₂ t ^ 2 ≤ C * X * Real.log X ^ 4) ∧
    ∀ t ∈ Set.Icc X (4 * X),
      |zetaMeanError t - (∑ n ∈ upTo X, atkinsonTerm n t) - S₂ t| ≤ C * Real.log t ^ 2

/-- `F(t) = t^{-1/2} E(t²)` of §6. -/
noncomputable def zetaMeanF (t : ℝ) : ℝ := t ^ (-(1 : ℝ) / 2) * zetaMeanError (t ^ 2)

open Classical in
/-- The almost-periodic coefficients of §6:
`aₙ(t) = μ²(n) (2/π)^{1/4} ∑_{r ≥ 1} (−1)^{n r} d(n r²) (n r²)^{-3/4} cos (2π r t − π/4)`. -/
noncomputable def zetaMeanOscCoeff (n : ℕ) (t : ℝ) : ℝ :=
  (if Squarefree n then 1 else 0) * (2 / Real.pi) ^ ((1 : ℝ) / 4) *
    ∑' r : ℕ, (-1 : ℝ) ^ (n * (r + 1)) *
      (divisorCount (n * (r + 1) ^ 2) : ℝ) / ((n * (r + 1) ^ 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 4) *
      Real.cos (2 * Real.pi * ((r + 1 : ℕ) : ℝ) * t - Real.pi / 4)

/-- `γₙ = √(2n/π)` of §6. -/
noncomputable def zetaMeanGamma (n : ℕ) : ℝ := Real.sqrt (2 * n / Real.pi)

/-- **§6**: for `1 ≤ N ≤ T^{1/8}` (i.e. `N ≤ X^{1/16}` with `X = T²`),
`T⁻¹ ∫_T^{2T} |F(t) − ∑_{n ≤ N} aₙ(γₙ t)| dt ≪ N^{-1/8}`. -/
def heathBrown_zetaMeanApprox : Prop :=
  ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ), 1 ≤ T → 1 ≤ N → (N : ℝ) ≤ T ^ ((1 : ℝ) / 8) →
    (1 / T) * (∫ t in T..(2 * T), |zetaMeanF t - oscSum zetaMeanOscCoeff zetaMeanGamma N t|) ≤
      C * (N : ℝ) ^ (-(1 : ℝ) / 8)

/-- **§6**: `F(t) = t^{-1/2} E(t²)` satisfies Hypothesis (H) with the `aₙ`,
`γₙ` above, and the hypotheses of Theorem 5 (with `μ = 5/3`) hold for the
subfamily indexed by square-free `n` (cf. `heathBrown_divisorHypothesisH`). -/
def heathBrown_zetaMeanHypothesisH : Prop :=
  HypothesisH zetaMeanF (reindex Squarefree zetaMeanOscCoeff) (reindex Squarefree zetaMeanGamma) ∧
    LinearIndependent ℚ (fun n : ℕ => reindex Squarefree zetaMeanGamma (n + 1)) ∧
    Theorem5Hypotheses (reindex Squarefree zetaMeanOscCoeff) ((5 : ℝ) / 3)

/-- **Heath-Brown–Huxley** (quoted in §6): `E(T) ≪_ε T^{7/22 + ε}`. -/
def heathBrownHuxley_zetaMeanBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → |zetaMeanError T| ≤ C * T ^ ((7 : ℝ) / 22 + ε)

/-- **§6** (Ivić, Theorem 15.7, with Heath-Brown–Huxley inserted):
`∫₀ᵀ |E(t)|ᴷ dt ≪_ε T^{1 + K/4 + ε}` with `K = 28/3`. -/
def heathBrown_zetaMeanMomentBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
    ∫ t in (0 : ℝ)..T, |zetaMeanError t| ^ ((28 : ℝ) / 3) ≤ C * T ^ (1 + (28 : ℝ) / 12 + ε)

/-! ### §7: the Piltz divisor problem for `d₃` -/

/-- The truncated Atkinson sum
`(x^{1/3} / (π √3)) ∑_{n ≤ T³/x} d₃(n) n^{-2/3} cos (6π ∛(n x))`. -/
noncomputable def atkinsonPiltz3Sum (T x : ℝ) : ℝ :=
  x ^ ((1 : ℝ) / 3) / (Real.pi * Real.sqrt 3) *
    ∑ n ∈ upTo (T ^ 3 / x), (piltz3 n : ℝ) / (n : ℝ) ^ ((2 : ℝ) / 3) *
      Real.cos (6 * Real.pi * (n * x) ^ ((1 : ℝ) / 3))

/-- **Atkinson's formula for `Δ₃`** as quoted in §7 (Titchmarsh (12.4.6)),
with Atkinson's range condition `x^{1/2+ε} ≤ T ≤ x^{2/3−ε}` restored:
`Δ₃(x) = (x^{1/3} / (π √3)) ∑_{n ≤ T³/x} d₃(n) n^{-2/3} cos (6π ∛(n x)) + O(x^{1+ε} / T)`. -/
def atkinson_piltz3Formula : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x →
    x ^ ((1 : ℝ) / 2 + ε) ≤ T → T ≤ x ^ ((2 : ℝ) / 3 - ε) →
    |piltz3Error x - atkinsonPiltz3Sum T x| ≤ C * x ^ (1 + ε) / T

/-- `ε(n) = 1` if `n` is cube-free, `0` otherwise. -/
def CubeFree (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ n

/-- `F(t) = t⁻¹ Δ₃(t³)` of §7. -/
noncomputable def piltz3F (t : ℝ) : ℝ := t⁻¹ * piltz3Error (t ^ 3)

open Classical in
/-- The almost-periodic coefficients of §7:
`aₙ(t) = (ε(n) / (π √3)) ∑_{r ≥ 1} d₃(n r³) (n r³)^{-2/3} cos (6π r t)`. -/
noncomputable def piltz3OscCoeff (n : ℕ) (t : ℝ) : ℝ :=
  (if CubeFree n then 1 else 0) / (Real.pi * Real.sqrt 3) *
    ∑' r : ℕ, (piltz3 (n * (r + 1) ^ 3) : ℝ) / ((n * (r + 1) ^ 3 : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
      Real.cos (6 * Real.pi * ((r + 1 : ℕ) : ℝ) * t)

/-- `γₙ = ∛n` of §7. -/
noncomputable def piltz3Gamma (n : ℕ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3)

/-- A smooth weight `ω ≥ 0` supported in `[1/2, 17/2]` with `ω = 1` on `[1, 8]`
(§7). -/
def Piltz3Weight (ω : ℝ → ℝ) : Prop :=
  (∀ k : ℕ, ContDiff ℝ k ω) ∧ (∀ x, 0 ≤ ω x) ∧
    (∀ x, ω x ≠ 0 → x ∈ Set.Icc ((1 : ℝ) / 2) ((17 : ℝ) / 2)) ∧
    ∀ x ∈ Set.Icc (1 : ℝ) 8, ω x = 1

/-- **§7, main estimate**: for every weight `ω` as above and `1 ≤ N ≤ T^{1/24}`,
`∫₀^∞ |F(t) − ∑_{n ≤ N} aₙ(γₙ t)|² ω((t/T)³) dt ≪_ω T N^{-1/4}`. -/
def heathBrown_piltz3MeanSquareApprox : Prop :=
  ∀ ω : ℝ → ℝ, Piltz3Weight ω → ∃ C : ℝ, ∀ (T : ℝ) (N : ℕ),
    1 ≤ T → 1 ≤ N → (N : ℝ) ≤ T ^ ((1 : ℝ) / 24) →
    ∫ t in Set.Ioi (0 : ℝ),
        (piltz3F t - oscSum piltz3OscCoeff piltz3Gamma N t) ^ 2 * ω ((t / T) ^ 3) ≤
      C * T * (N : ℝ) ^ (-(1 : ℝ) / 4)

/-- **§7**: `F(t) = t⁻¹ Δ₃(t³)` satisfies Hypothesis (H) with the `aₙ`, `γₙ`
above, and the hypotheses of Theorem 5 with `μ = 3/2` hold for the subfamily
indexed by cube-free `n` (`aₙ ≡ 0` otherwise, and `∛8 = 2 ∛1`; the cube roots
of the cube-free integers are `ℚ`-linearly independent). -/
def heathBrown_piltz3HypothesisH : Prop :=
  HypothesisH piltz3F (reindex CubeFree piltz3OscCoeff) (reindex CubeFree piltz3Gamma) ∧
    LinearIndependent ℚ (fun n : ℕ => reindex CubeFree piltz3Gamma (n + 1)) ∧
    Theorem5Hypotheses (reindex CubeFree piltz3OscCoeff) ((3 : ℝ) / 2)

/-- **(7.9)** with exponent `K`: `∫₀ˣ |Δ₃(x)|ᴷ dx ≪_ε X^{1 + K/3 + ε}`. -/
def piltz3MomentBound (K : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X →
    ∫ x in (0 : ℝ)..X, |piltz3Error x| ^ K ≤ C * X ^ (1 + K / 3 + ε)

/-- **Heath-Brown, Lemma 6**: `∫₀ˣ |Δ₃(x)|³ dx ≪_ε X^{2 + ε}`, i.e. (7.9)
with `K = 3`. -/
def heathBrown_lemma6 : Prop := piltz3MomentBound 3

/-! ### Cited background, §1 -/

/-- **(1.2)** (Cramér): `X^{-3/2} ∫₀ˣ Δ(x)² dx → (6π²)⁻¹ ∑ d(n)² n^{-3/2}`. -/
def cramer_divisorMeanSquare : Prop :=
  Filter.Tendsto (fun X : ℝ => X ^ (-(3 : ℝ) / 2) * ∫ x in (0 : ℝ)..X, divisorError x ^ 2)
    Filter.atTop
    (nhds ((6 * Real.pi ^ 2)⁻¹ *
      ∑' n : ℕ, (divisorCount (n + 1) : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))

/-- **Voronoï** (quoted in §1): `∫₀ˣ Δ(x) dx = o(X^{5/4})`. -/
def voronoi_divisorFirstMoment : Prop :=
  Filter.Tendsto (fun X : ℝ => X ^ (-(5 : ℝ) / 4) * ∫ x in (0 : ℝ)..X, divisorError x)
    Filter.atTop (nhds 0)

/-- **Tsang** (quoted in §1): the third and fourth moments (1.1) of `Δ(x)`
converge. -/
def tsang_divisorMoments : Prop :=
  SignedMomentConverges ((1 : ℝ) / 4) 3 divisorError ∧
    SignedMomentConverges ((1 : ℝ) / 4) 4 divisorError

/-- **Cramér** (quoted in §1): `X^{-3/2} ∫₀ˣ P(x)² dx → (3π²)⁻¹ ∑ r(n)² n^{-3/2}`. -/
def cramer_circleMeanSquare : Prop :=
  Filter.Tendsto (fun X : ℝ => X ^ (-(3 : ℝ) / 2) * ∫ x in (0 : ℝ)..X, circleError x ^ 2)
    Filter.atTop
    (nhds ((3 * Real.pi ^ 2)⁻¹ *
      ∑' n : ℕ, (sumTwoSquaresCount (n + 1) : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))

/-- **Tsang** (quoted in §1): the third and fourth moments of `P(x)` converge. -/
def tsang_circleMoments : Prop :=
  SignedMomentConverges ((1 : ℝ) / 4) 3 circleError ∧
    SignedMomentConverges ((1 : ℝ) / 4) 4 circleError

/-- **(1.3)** (Heath-Brown [4]):
`T^{-3/2} ∫₀ᵀ E(t)² dt → (2/3) (2π)^{-1/2} ∑ d(n)² n^{-3/2}`. -/
def heathBrown_zetaMeanSquare : Prop :=
  Filter.Tendsto (fun T : ℝ => T ^ (-(3 : ℝ) / 2) * ∫ t in (0 : ℝ)..T, zetaMeanError t ^ 2)
    Filter.atTop
    (nhds ((2 : ℝ) / 3 * (2 * Real.pi) ^ (-(1 : ℝ) / 2) *
      ∑' n : ℕ, (divisorCount (n + 1) : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))

/-- **Tsang** (quoted in §1): the third and fourth moments of `E(t)` converge. -/
def tsang_zetaMeanMoments : Prop :=
  SignedMomentConverges ((1 : ℝ) / 4) 3 zetaMeanError ∧
    SignedMomentConverges ((1 : ℝ) / 4) 4 zetaMeanError

/-- **(1.4)** (Tong; Ivić (13.43)):
`X^{-5/3} ∫₀ˣ Δ₃(x)² dx = (10π²)⁻¹ ∑ d₃(n)² n^{-4/3} + O_ε(X^{-1/9 + ε})`. -/
def tong_piltz3MeanSquare : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X →
    |X ^ (-(5 : ℝ) / 3) * (∫ x in (0 : ℝ)..X, piltz3Error x ^ 2) -
        (10 * Real.pi ^ 2)⁻¹ *
          ∑' n : ℕ, (piltz3 (n + 1) : ℝ) ^ 2 / ((n + 1 : ℕ) : ℝ) ^ ((4 : ℝ) / 3)| ≤
      C * X ^ (-(1 : ℝ) / 9 + ε)

end LeanProofs.IntegerPoints
