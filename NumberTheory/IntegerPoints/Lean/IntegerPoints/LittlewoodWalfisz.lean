import IntegerPoints.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Littlewood–Walfisz, *The lattice points of a circle*

Formal statements (no proofs) of the results of

> J. E. Littlewood and A. Walfisz, The lattice points of a circle (with a
> note by E. Landau), Proc. Roy. Soc. London A 106 (1924), 478–488,

transcribed in `Papers/The Lattice Points of a Circle.tex`.

The paper proves `R(x) - π x = O(x^{37/112 + ε})` for the lattice-point
count `R(x)` of the circle, through Lemmas 1–6; Landau's appended note
refines this to `O(x^{37/112} log^{5/56} x)` starting from the classical
integrated formula (8.1).  We also state the cited background (1.1)–(1.4).

## Conventions

* `R(x)` is `latticeCount x` and `R(x) - π x` is `circleError x`
  (`IntegerPoints.Basic`); `r(n)` is `sumTwoSquaresCount n`.
* `s = x^{75/112}` is `lwS x`; `z = 2 π √x u^{1/(2s)}` is `lwZ x u`.
* `a_n` of (2.1) is `lwCoefficient x n`.
* `O`-bounds with constants depending on `ε` (or `α`) are written
  `∀ ε > 0, ∃ C x₀, ∀ x ≥ x₀, …`; the paper's `c₁, …, c₄₃` become
  existentially quantified constants.
* `e^{i t}` for real `t` is `eI t`.  The "Min" of Lemma 6, equal to `ν₂`
  when the cosecant is infinite, is `minCosec`.
* Infinite series over `n ≥ 1` are Mathlib's `∑'` of the term at `n + 1`;
  each series so written converges absolutely (`r(n) = O(n^ε)` and the
  decay of `a_n` in `n`, or the exponent `5/4 > 1`), so this is faithful.
* The divisor problem of (1.3) uses the standard main term
  `x log x + (2γ - 1) x` for the unspecified elementary function `D₀(x)`.
-/

open scoped BigOperators
open Real Finset Filter Asymptotics MeasureTheory

namespace LeanProofs.IntegerPoints

/-! ### Helper notions -/

/-- `e^{i t}` for real `t`. -/
noncomputable def eI (t : ℝ) : ℂ := Complex.exp (Complex.I * (t : ℂ))

/-- `d(n)`, the number of positive divisors of `n`. -/
def numDivisors (n : ℕ) : ℕ := (Nat.divisors n).card

/-- `D(x) = ∑_{n ≤ x} d(n)`. -/
noncomputable def divisorSumStd (x : ℝ) : ℕ := ∑ n ∈ upTo x, numDivisors n

/-- `D(x) - x log x - (2γ - 1) x`, the error term of the divisor problem
with the standard main term. -/
noncomputable def divisorErrorStd (x : ℝ) : ℝ :=
  (divisorSumStd x : ℝ) - (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)

/-- `s = x^{75/112}` (§2). -/
noncomputable def lwS (x : ℝ) : ℝ := x ^ ((75 : ℝ) / 112)

/-- `z = 2 π √x u^{1/(2s)}` (§4). -/
noncomputable def lwZ (x u : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt x * u ^ (1 / (2 * lwS x))

/-- **(2.1)**: `a_n = ∫₀^∞ e^{-u} u^{1/(4s)} cos(2π√(nx) u^{1/(2s)} - 3π/4) du`. -/
noncomputable def lwCoefficient (x : ℝ) (n : ℕ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ),
    Real.exp (-u) * u ^ (1 / (4 * lwS x)) *
      Real.cos (2 * Real.pi * Real.sqrt ((n : ℝ) * x) * u ^ (1 / (2 * lwS x)) -
        3 * Real.pi / 4)

/-- The weight `r(n) / n^{3/4}`. -/
noncomputable def rWeight34 (n : ℕ) : ℝ :=
  (sumTwoSquaresCount n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 4)

/-- The weight `r(n) / n^{5/4}`. -/
noncomputable def rWeight54 (n : ℕ) : ℝ :=
  (sumTwoSquaresCount n : ℝ) / (n : ℝ) ^ ((5 : ℝ) / 4)

open Classical in
/-- `Min(ν, |cosec t|)` of Lemma 6, read as `ν` when the cosecant is
infinite. -/
noncomputable def minCosec (ν t : ℝ) : ℝ :=
  if Real.sin t = 0 then ν else min ν |1 / Real.sin t|

/-! ### Cited background, §1 -/

/-- **(1.1)** (trivial): `R(x) - π x = O(x^{1/2})`. -/
def lw_trivialBound : Prop :=
  circleError =O[atTop] fun x : ℝ => x ^ ((1 : ℝ) / 2)

/-- **Hardy, Landau (1915)**: `R(x) - π x = O(x^α)` is false for every
`α < 1/4`. -/
def hardyLandau_noBoundBelowQuarter : Prop :=
  ∀ α : ℝ, α < 1 / 4 → ¬ (circleError =O[atTop] fun x : ℝ => x ^ α)

/-- **Sierpiński's bound**, "known for some time": `R(x) - π x = O(x^{1/3})`. -/
def lw_oneThirdBound : Prop :=
  circleError =O[atTop] fun x : ℝ => x ^ ((1 : ℝ) / 3)

/-- **(1.2)** (van der Corput, 1923): `R(x) - π x = O(x^{Θ + ε})` for some
constant `Θ < 1/3` and every `ε > 0`. -/
def vanDerCorput_circleBound : Prop :=
  ∃ Θ : ℝ, Θ < 1 / 3 ∧
    ∀ ε : ℝ, 0 < ε → circleError =O[atTop] fun x : ℝ => x ^ (Θ + ε)

/-- **(1.3)** (van der Corput, 1922): `D(x) - D₀(x) = O(x^{Θ + ε})` for some
constant `Θ < 33/100` and every `ε > 0`, with `D₀` the standard main term. -/
def vanDerCorput_divisorBound : Prop :=
  ∃ Θ : ℝ, Θ < 33 / 100 ∧
    ∀ ε : ℝ, 0 < ε → divisorErrorStd =O[atTop] fun x : ℝ => x ^ (Θ + ε)

/-- **(1.4)** (Hardy–Littlewood): `ζ(1/2 + it) = O(t^{1/6 + ε})`. -/
def hardyLittlewood_zetaSixth : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
    ‖riemannZeta (1 / 2 + Complex.I * (t : ℂ))‖ ≤ C * t ^ ((1 : ℝ) / 6 + ε)

/-! ### The main theorem -/

/-- **Littlewood–Walfisz, main theorem** ((1.2) with (1.5)):
`R(x) - π x = O(x^{37/112 + ε})` for every `ε > 0`. -/
def littlewoodWalfisz_theorem : Prop :=
  ∀ ε : ℝ, 0 < ε → circleError =O[atTop] fun x : ℝ => x ^ ((37 : ℝ) / 112 + ε)

/-! ### Lemmas 1–4 -/

/-- **Lemma 1** (after Wigert):
`R(x) - π x = π⁻¹ x^{1/4} ∑_{n ≥ 1} r(n) n^{-3/4} a_n + O(x^{37/112 + ε})`. -/
def lw_lemma1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |circleError x -
        (1 / Real.pi) * x ^ ((1 : ℝ) / 4) *
          ∑' n : ℕ, rWeight34 (n + 1) * lwCoefficient x (n + 1)| ≤
      C * x ^ ((37 : ℝ) / 112 + ε)

/-- **Lemma 2**:
`R(x) - π x = π⁻¹ x^{1/4} ∑_{n ≤ x^{19/56 + ε}} r(n) n^{-3/4} a_n + O(x^{37/112 + ε})`. -/
def lw_lemma2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |circleError x -
        (1 / Real.pi) * x ^ ((1 : ℝ) / 4) *
          ∑ n ∈ upTo (x ^ ((19 : ℝ) / 56 + ε)), rWeight34 n * lwCoefficient x n| ≤
      C * x ^ ((37 : ℝ) / 112 + ε)

/-- **Lemma 3**, (4.1):
`R(x) - π x = π⁻¹ x^{1/4} ∫_{1/x}^{x} e^{-u} u^{1/(4s)}
   ∑_{n ≤ x^{19/56 + ε}} r(n) n^{-3/4} cos(z √n - 3π/4) du + O(x^{37/112 + ε})`
with `z = 2π√x u^{1/(2s)}`. -/
def lw_lemma3 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |circleError x -
        (1 / Real.pi) * x ^ ((1 : ℝ) / 4) *
          ∫ u in x⁻¹..x,
            Real.exp (-u) * u ^ (1 / (4 * lwS x)) *
              ∑ n ∈ upTo (x ^ ((19 : ℝ) / 56 + ε)),
                rWeight34 n * Real.cos (lwZ x u * Real.sqrt n - 3 * Real.pi / 4)| ≤
      C * x ^ ((37 : ℝ) / 112 + ε)

/-- **Lemma 4**, (5.1): for `19/56 + ε ≤ 2/3`, uniformly in `1/x ≤ u ≤ x`,
`∑_{n ≤ x^{19/56 + ε}} r(n) n^{-3/4} e^{i z √n} = O(x^{9/112 + ε})`. -/
def lw_lemma4 : Prop :=
  ∀ ε : ℝ, 0 < ε → (19 : ℝ) / 56 + ε ≤ 2 / 3 →
    ∃ C x₀ : ℝ, ∀ x u : ℝ, x₀ ≤ x → x⁻¹ ≤ u → u ≤ x →
      ‖∑ n ∈ upTo (x ^ ((19 : ℝ) / 56 + ε)),
          (rWeight34 n : ℂ) * eI (lwZ x u * Real.sqrt n)‖ ≤
        C * x ^ ((9 : ℝ) / 112 + ε)

/-! ### Lemma 5 (the Hardy–Littlewood method) -/

/-- The sum `∑_{q = Q}^{Q'} e^{i z √(p² + q²)}` of Lemma 5. -/
noncomputable def lwCircleSum (z : ℝ) (p Q Q' : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc Q Q', eI (z * Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2))

/-- **Lemma 5**, (5.2): let `α > 0`, `0 ≤ τ ≤ 1/3`, `x^τ/√2 ≤ Q ≤ Q' ≤ 2x^τ`,
`0 < p ≤ Q` (`Q, Q'` integers), and `z = 2π√x u^{1/(2s)}` with
`1/x ≤ u ≤ x`.  Then
`|∑_{q=Q}^{Q'} e^{i z √(p² + q²)}|
   ≤ c₁ (x^{9τ/10 + 1/80 + α} + p^{-1/4} x^{49τ/40 - 1/80 + α})`,
where `c₁` depends only on `α`. -/
def lw_lemma5 : Prop :=
  ∀ α : ℝ, 0 < α → ∃ c₁ : ℝ, ∀ (x u τ : ℝ) (p Q Q' : ℕ),
    2 ≤ x → x⁻¹ ≤ u → u ≤ x → 0 ≤ τ → τ ≤ 1 / 3 →
    x ^ τ / Real.sqrt 2 ≤ Q → Q ≤ Q' → (Q' : ℝ) ≤ 2 * x ^ τ → 0 < p → p ≤ Q →
    ‖lwCircleSum (lwZ x u) p Q Q'‖ ≤
      c₁ * (x ^ (9 * τ / 10 + 1 / 80 + α) +
            (p : ℝ) ^ (-(1 : ℝ) / 4) * x ^ (49 * τ / 40 - 1 / 80 + α))

/-! ### Lemma 6 (Weyl's inequality) -/

/-- The real polynomial `P(y) = β₀ y^b + β₁ y^{b-1} + ⋯ + β_b` with
coefficient sequence `β`. -/
noncomputable def lwPoly (b : ℕ) (β : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (b + 1), β i * y ^ (b - i)

/-- The integer tuples `(m₁, …, m_{b-1})` with `|m₁| + ⋯ + |m_{b-1}| ≤ ν₂ - 1`. -/
noncomputable def weylTuples (b ν₂ : ℕ) : Finset (Fin (b - 1) → ℤ) :=
  (Fintype.piFinset fun _ : Fin (b - 1) => Finset.Icc (-(ν₂ : ℤ) + 1) ((ν₂ : ℤ) - 1)).filter
    fun m => ∑ i, |m i| ≤ (ν₂ : ℤ) - 1

/-- **Lemma 6** (Weyl, in Landau's form): for an integer `b ≥ 2`, a real
polynomial `P(y) = β₀ y^b + ⋯ + β_b`, real `ψ`, integers `ν₁` and `ν₂ ≥ 1`,
`|∑_{m=ν₁+1}^{ν₁+ν₂} e^{i ψ P(m)}|^{2^{b-1}}
   ≤ (2ν₂)^{2^{b-1} - b} ∑_{|m₁| + ⋯ + |m_{b-1}| ≤ ν₂ - 1}
       Min{ν₂, |cosec(½ ψ β₀ b! m₁ ⋯ m_{b-1})|}`. -/
def weyl_lemma6 : Prop :=
  ∀ (b : ℕ) (β : ℕ → ℝ) (ψ : ℝ) (ν₁ : ℤ) (ν₂ : ℕ), 2 ≤ b → 1 ≤ ν₂ →
    ‖∑ m ∈ Finset.Icc (ν₁ + 1) (ν₁ + (ν₂ : ℤ)), eI (ψ * lwPoly b β (m : ℝ))‖ ^ (2 ^ (b - 1)) ≤
      (2 * (ν₂ : ℝ)) ^ (2 ^ (b - 1) - b) *
        ∑ m ∈ weylTuples b ν₂,
          minCosec (ν₂ : ℝ)
            (ψ * β 0 * (Nat.factorial b : ℝ) * (∏ i, (m i : ℝ)) / 2)

/-! ### §7, the dyadic estimate (7.2) -/

/-- **(7.2)**: for `0 ≤ τ ≤ 1/3` and `z` as in Lemma 5,
`|∑_{x^{2τ} < n ≤ 4x^{2τ}} r(n) e^{i z √n}| ≤ c₂₅ x^{19τ/10 + 1/80 + α}`,
with `c₂₅` depending only on `α > 0`. -/
def lw_dyadicEstimate : Prop :=
  ∀ α : ℝ, 0 < α → ∃ c₂₅ : ℝ, ∀ x u τ : ℝ,
    2 ≤ x → x⁻¹ ≤ u → u ≤ x → 0 ≤ τ → τ ≤ 1 / 3 →
    ‖∑ n ∈ intRange (x ^ (2 * τ)) (4 * x ^ (2 * τ)),
        (sumTwoSquaresCount n : ℂ) * eI (lwZ x u * Real.sqrt n)‖ ≤
      c₂₅ * x ^ (19 * τ / 10 + 1 / 80 + α)

/-! ### Landau's note, §8 -/

/-- **(8.1)** (classical):
`∫₀^x (R(y) - π y) dy = -c₃₁ x^{3/4} ∑_{n ≥ 1} r(n) n^{-5/4} cos(2π√(nx) - π/4) + O(x^{1/4})`
for a positive constant `c₃₁` (in fact `c₃₁ = 1/π²`). -/
def landau_integratedFormula : Prop :=
  ∃ c₃₁ : ℝ, 0 < c₃₁ ∧ ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |(∫ y in (0 : ℝ)..x, circleError y) +
        c₃₁ * x ^ ((3 : ℝ) / 4) *
          ∑' n : ℕ, rWeight54 (n + 1) *
            Real.cos (2 * Real.pi * Real.sqrt (((n : ℝ) + 1) * x) - Real.pi / 4)| ≤
      C * x ^ ((1 : ℝ) / 4)

/-- **Landau's refinement**: `R(x) - π x = O(x^{37/112} log^{5/56} x)`. -/
def landau_refinedTheorem : Prop :=
  circleError =O[atTop] fun x : ℝ =>
    x ^ ((37 : ℝ) / 112) * Real.log x ^ ((5 : ℝ) / 56)

/-- The sum `∑_{q = Q}^{Q'} e^{2πi √y √(p² + q²)} / (p² + q²)^j` of (8.2)
(`j = 0` gives the unweighted sum). -/
noncomputable def landauCircleSum (y j : ℝ) (p Q Q' : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc Q Q',
    e (Real.sqrt y * Real.sqrt ((p : ℝ) ^ 2 + (q : ℝ) ^ 2)) /
      ((((p : ℝ) ^ 2 + (q : ℝ) ^ 2) ^ j : ℝ) : ℂ)

/-- **Landau's form of Lemma 5**: for `y > 1` and `1 ≤ p < Q ≤ Q' < 2Q`,
`|∑_{q=Q}^{Q'} e^{2πi √y √(p² + q²)}|
   < c₃₂ (y^{1/80} Q^{9/10} log^{1/8} Q + y^{-1/80} p^{-1/4} Q^{49/40} log^{1/2} Q)`. -/
def landau_circleSumBound : Prop :=
  ∃ c₃₂ : ℝ, ∀ (y : ℝ) (p Q Q' : ℕ), 1 < y → 1 ≤ p → p < Q → Q ≤ Q' → Q' < 2 * Q →
    ‖landauCircleSum y 0 p Q Q'‖ <
      c₃₂ * (y ^ ((1 : ℝ) / 80) * (Q : ℝ) ^ ((9 : ℝ) / 10) * Real.log Q ^ ((1 : ℝ) / 8) +
             y ^ (-(1 : ℝ) / 80) * (p : ℝ) ^ (-(1 : ℝ) / 4) * (Q : ℝ) ^ ((49 : ℝ) / 40) *
               Real.log Q ^ ((1 : ℝ) / 2))

/-- **(8.2)** (with `c₃₃`, valid without `Q' < 2Q`): for `y > 1`,
`1 ≤ p < Q ≤ Q'` and `j ∈ {3/4, 5/4}`,
`|∑_{q=Q}^{Q'} e^{2πi √y √(p² + q²)} / (p² + q²)^j|
   < c₃₃ (y^{1/80} Q^{9/10 - 2j} log^{1/8} Q + y^{-1/80} p^{-1/4} Q^{49/40 - 2j} log^{1/2} Q)`. -/
def landau_weightedCircleSumBound : Prop :=
  ∃ c₃₃ : ℝ, ∀ (y j : ℝ) (p Q Q' : ℕ), 1 < y → (j = 3 / 4 ∨ j = 5 / 4) →
    1 ≤ p → p < Q → Q ≤ Q' →
    ‖landauCircleSum y j p Q Q'‖ <
      c₃₃ * (y ^ ((1 : ℝ) / 80) * (Q : ℝ) ^ ((9 : ℝ) / 10 - 2 * j) *
               Real.log Q ^ ((1 : ℝ) / 8) +
             y ^ (-(1 : ℝ) / 80) * (p : ℝ) ^ (-(1 : ℝ) / 4) *
               (Q : ℝ) ^ ((49 : ℝ) / 40 - 2 * j) * Real.log Q ^ ((1 : ℝ) / 2))

/-- **(8.3)**: for `2 ≤ ω ≤ y^{1/2}`,
`|∑_{n ≤ ω} r(n) n^{-3/4} e^{2πi √(ny)}| < c₃₇ y^{1/80} ω^{1/5} log^{1/8} y`. -/
def landau_83 : Prop :=
  ∃ c₃₇ : ℝ, ∀ y ω : ℝ, 2 ≤ ω → ω ≤ y ^ ((1 : ℝ) / 2) →
    ‖∑ n ∈ upTo ω, (rWeight34 n : ℂ) * e (Real.sqrt ((n : ℝ) * y))‖ <
      c₃₇ * y ^ ((1 : ℝ) / 80) * ω ^ ((1 : ℝ) / 5) * Real.log y ^ ((1 : ℝ) / 8)

open Classical in
/-- **(8.4)**: for `2 ≤ ω ≤ y^{1/2}`,
`|∑_{n > ω} r(n) n^{-5/4} e^{2πi √(ny)}| < c₄₂ y^{1/80} ω^{-3/10} log^{1/8} y`. -/
def landau_84 : Prop :=
  ∃ c₄₂ : ℝ, ∀ y ω : ℝ, 2 ≤ ω → ω ≤ y ^ ((1 : ℝ) / 2) →
    ‖∑' n : ℕ, if ω < (n : ℝ) then (rWeight54 n : ℂ) * e (Real.sqrt ((n : ℝ) * y)) else 0‖ <
      c₄₂ * y ^ ((1 : ℝ) / 80) * ω ^ (-(3 : ℝ) / 10) * Real.log y ^ ((1 : ℝ) / 8)

end LeanProofs.IntegerPoints
