import IntegerPoints.ExponentialSums
import Mathlib.Analysis.Convex.Hull
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Huxley, *Exponential sums and lattice points III*

Formal statements (no proofs) of the numbered results of

> M. N. Huxley, Exponential sums and lattice points III,
> Proc. London Math. Soc. (3) 87 (2003), 591–609,

transcribed in `Papers/Exponential sums and lattice points III.tex`:
Hypothesis `H(κ, λ)`, Propositions 1–6 (conditional on `H(κ, λ)`),
Theorems 1–6 (their unconditional forms with `κ = 3/10`, `λ = 57/140`), the
Corollary to Proposition 3, the headline bounds of §1 for the Gauss circle and
Dirichlet divisor problems (`K = 131/208`, `Λ = 18627/8320`), and the
Farey-arc counting lemmas of §2 (Lemmas 2.3–2.5).

Every statement is a `Prop`-valued definition; nothing is asserted.

## Conventions

* `≪` / `O(·)` are rendered with explicit constants: constants that the paper
  says are "constructed from `C₁, …, κ, λ, g, G`" are existentially quantified
  *after* those data (`∀ C₁ … ∃ B₁ B₂ …`); "large parameters" are bounded
  below by an existentially quantified threshold `P₀`.
* `F` is taken globally `C³` (or `C⁴`) on `ℝ` with the bounds (1.5)–(1.7),
  (1.29) imposed on `[1, 2]`; `deriv`/`iteratedDeriv` are the classical
  derivatives there (see the conventions of `IntegerPoints.ExponentialSums`).
* Functions "of bounded variation" on `[1, 2]` are encoded by
  `BVBounded K g`: `|g| ≤ K` on `[1, 2]` and `eVariationOn g [1, 2] ≤ K`.
* Each conditional proposition is split into `huxley_propN_conclusion κ λ`
  (the statement for given `κ, λ`) and `huxley_propN` (`H(κ, λ)` implies the
  conclusion for `1/4 ≤ κ ≤ 1/3`, `λ ≥ 0`); Theorem `N` is then the conclusion
  at `κ = 3/10`, `λ = 57/140`.
* Lattice points "in `M Ω`" for an isometric embedding are counted by
  `latticeCountIn Ω M θ σ a b`: the integer points `(m, n)` that are images of
  points of `Ω` under the rigid motion `p ↦ M R_θ (p₁, σ p₂) + (a, b)`,
  `σ = ±1` (rotation, optional reflection, translation, dilation by `M`).
* The convex domain of Proposition 5 is encoded by its radius of curvature
  as a function of the tangent angle (`SmoothConvexCurve`): the boundary is
  `ψ ↦ ∫₀^ψ ρ(θ)(cos θ, sin θ) dθ`, the domain is the convex hull of the
  boundary, and the area is its Lebesgue measure.
* The "rounding error" sums use the row-of-teeth function
  `ρ(t) = [t] - t + 1/2` (`rowOfTeeth`).

## Notes on the transcription

* (1.19): the printed exponent `(51κ - 1)/(33κ - 3)` of `M` must be
  `(51κ - 5)/(33κ - 3)`: it is the condition `H ≤ N` for the choice (3.22)
  and agrees with (1.43); corrected in the tex (marked `% ed.:`).
* §1: `Λ = 18627/8320 = 2.2388…`, not `2.2513…`; corrected in the tex.
* Corollary to Proposition 3: the printed wider range `1 - 1/(2M) ≤ x ≤ 1 + 1/(2M)`
  is read as `1 - 1/(2M) ≤ x ≤ 2 + 1/(2M)` (the integral in (1.28) needs `F`
  on `[1 - 1/(2M), 2 - 1/(2M)]`); corrected in the tex and used in
  `WiderRangeBounds`.
* §2: the phase of the Farey dissection is `f(x) = (T/M) F(x/M)`, not
  `T F(x/M)`: (2.2) says `R² ≍ M³/(N T)`, i.e. `|f''| ≍ T/M³`, and the remark
  after (2.10) says `f' ≍ T/M²`.  With `T F(x/M)` the hypotheses (2.1) and
  (2.2) would be incompatible for large `M`.
* §2: only the short intervals contained in `[M, 2M]` are indexed
  (`shortIndices`); an interval protruding beyond `2M`, where `F` is
  unconstrained, could carry an arbitrarily large Farey label and falsify the
  counting bounds.
* Proposition 4 leaves the logarithm exponent `A` in (1.30) unspecified
  ("calculated from `κ` and `λ`"); it is existentially quantified here.
* Lemma 2.4 uses the bad intervals (2.9) `|f'(x) - c/k| ≤ η/(K Q')`, where
  `K` is not defined in this paper (it is a parameter of [11]).  We keep `K`
  as an explicit parameter and assume `Q' ≤ K`, the regime in which the bad
  set has relative measure `≪ η` and the bound (2.12) makes sense.
* Lemmas 2.3–2.5 count *all* short intervals of `[M, 2M]` whose Farey label
  has denominator in the stated range (the minor arcs form a subset, and the
  proofs bound the larger count); the label `a/q` of an interval is the
  reduced rational value of `f'` on it with `q ≥ R` minimal, as in §2.
* Lemma 2.1 (major arcs) and Lemmas 3.1–3.7 (First and Second Spacing
  Problems) bound quantities (`A`, `E`, `B'`, `V`, the major-arc
  contribution, "magic matrices") whose definitions are only in [9] and [11]
  and are not reproduced in this paper; they are not formalised here.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

/-! ### Helper notions -/

/-- The row-of-teeth function `ρ(t) = [t] - t + 1/2`. -/
noncomputable def rowOfTeeth (t : ℝ) : ℝ := (⌊t⌋ : ℝ) - t + 1 / 2

/-- The number of integer points `(m, n)` with `a ≤ m ≤ b` and `|n - f(m)| ≤ δ`. -/
noncomputable def closePointCount (f : ℝ → ℝ) (a b δ : ℝ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | a ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ b ∧ |(p.2 : ℝ) - f (p.1 : ℝ)| ≤ δ}

/-- `g` is bounded by `K` and of variation at most `K` on `[1, 2]`. -/
def BVBounded (K : ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (1 : ℝ) 2, |g x| ≤ K) ∧
    eVariationOn g (Set.Icc (1 : ℝ) 2) ≤ ENNReal.ofReal K

/-- **Hypothesis `H(κ, λ)`** (§1).  For `F` bounded and `C³` with
`F'' ≠ 0`, `F''' ≠ 0` on `[1, 2]`, `M ≥ 2`, `√M ≤ N ≤ M²`, `f(x) = N F(x/M)`
and `0 ≤ δ ≤ 1/2`, the number `R` of integer points `(m, n)` with
`|n - f(m)| ≤ δ`, `M ≤ m ≤ 2M`, satisfies
`R = O(δ M + (MN)^κ (log MN)^λ)`, the constant depending on `F` only through
upper and lower bounds for its derivatives. -/
def HuxleyHypothesisH (κ lam : ℝ) : Prop :=
  ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
    ∃ C : ℝ, ∀ (F : ℝ → ℝ) (M N δ : ℝ), ContDiff ℝ 3 F →
      (∀ x ∈ Set.Icc (1 : ℝ) 2,
        |F x| ≤ c₁ ∧ |deriv F x| ≤ c₁ ∧ |iteratedDeriv 2 F x| ≤ c₁ ∧
          |iteratedDeriv 3 F x| ≤ c₁ ∧
          c₂ ≤ |iteratedDeriv 2 F x| ∧ c₂ ≤ |iteratedDeriv 3 F x|) →
      2 ≤ M → Real.sqrt M ≤ N → N ≤ M ^ 2 → 0 ≤ δ → δ ≤ 1 / 2 →
      (closePointCount (fun x => N * F (x / M)) M (2 * M) δ : ℝ) ≤
        C * (δ * M + (M * N) ^ κ * Real.log (M * N) ^ lam)

/-! ### The derivative conditions (1.5)–(1.7), (1.29) -/

/-- `F` is `C³` with (1.5) for `r = 1, 2, 3` and (1.6) for `r = 1, 2` on `[1, 2]`. -/
def DerivConditions (C₁ C₂ C₃ : ℝ) (F : ℝ → ℝ) : Prop :=
  ContDiff ℝ 3 F ∧
    ∀ x ∈ Set.Icc (1 : ℝ) 2,
      |deriv F x| ≤ C₁ ∧ |iteratedDeriv 2 F x| ≤ C₂ ∧ |iteratedDeriv 3 F x| ≤ C₃ ∧
        1 / C₁ ≤ |deriv F x| ∧ 1 / C₂ ≤ |iteratedDeriv 2 F x|

/-- (1.6) for `r = 3`: `|F'''| ≥ 1/C₃` on `[1, 2]`. -/
def DerivLowerBound3 (C₃ : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (1 : ℝ) 2, 1 / C₃ ≤ |iteratedDeriv 3 F x|

/-- (1.7): `|F' F''' - 3 F''²| ≥ 1/C₄` on `[1, 2]`. -/
def Cond17 (C₄ : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (1 : ℝ) 2,
    1 / C₄ ≤ |deriv F x * iteratedDeriv 3 F x - 3 * iteratedDeriv 2 F x ^ 2|

/-- (1.29): `|F'' F'''' - 3 F'''²| ≥ 1/C₀` on `[1, 2]`. -/
def Cond129 (C₀ : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (1 : ℝ) 2,
    1 / C₀ ≤ |iteratedDeriv 2 F x * iteratedDeriv 4 F x - 3 * iteratedDeriv 3 F x ^ 2|

/-- The conditions of Proposition 4: `F` is `C⁴`, (1.5) for `r = 1, …, 4`
(with `C₄` bounding `F''''`), (1.6) for `r = 1, 2, 3`, (1.7) and (1.29). -/
def Prop4Conditions (C₀ C₁ C₂ C₃ C₄ : ℝ) (F : ℝ → ℝ) : Prop :=
  ContDiff ℝ 4 F ∧ DerivConditions C₁ C₂ C₃ F ∧
    (∀ x ∈ Set.Icc (1 : ℝ) 2, |iteratedDeriv 4 F x| ≤ C₄) ∧
    DerivLowerBound3 C₃ F ∧ Cond17 C₄ F ∧ Cond129 C₀ F

/-! ### The ranges (1.8), (1.11), (1.12), (1.15), (1.18) -/

/-- (1.8): `C₅⁻¹ T^{67κ-6} (log T)^{(45κ-4)λ} ≤ M^{156κ-14} ≤ C₅ T^{89κ-8} (log T)^{-(45κ-4)λ}`. -/
def range18 (κ lam C₅ M T : ℝ) : Prop :=
  C₅⁻¹ * T ^ (67 * κ - 6) * Real.log T ^ ((45 * κ - 4) * lam) ≤ M ^ (156 * κ - 14) ∧
    M ^ (156 * κ - 14) ≤ C₅ * T ^ (89 * κ - 8) * Real.log T ^ (-((45 * κ - 4) * lam))

/-- (1.11): `M^{156κ-14} ≤ C₅ T^{69κ-6} (log T)^{-3(9κ-1)λ}`. -/
def range111 (κ lam C₅ M T : ℝ) : Prop :=
  M ^ (156 * κ - 14) ≤ C₅ * T ^ (69 * κ - 6) * Real.log T ^ (-(3 * (9 * κ - 1) * lam))

/-- (1.12): `M^{156κ-14} ≥ C₅⁻¹ T^{87κ-8} (log T)^{3(9κ-1)λ}`. -/
def range112 (κ lam C₅ M T : ℝ) : Prop :=
  C₅⁻¹ * T ^ (87 * κ - 8) * Real.log T ^ (3 * (9 * κ - 1) * lam) ≤ M ^ (156 * κ - 14)

/-- (1.15): `C₅⁻¹ T^{1/3} ≤ M ≤ C₅ T^{7/16} (log T)^{3λ/16}`. -/
def range115 (lam C₅ M T : ℝ) : Prop :=
  C₅⁻¹ * T ^ ((1 : ℝ) / 3) ≤ M ∧ M ≤ C₅ * T ^ ((7 : ℝ) / 16) * Real.log T ^ (3 * lam / 16)

/-- (1.18): `C₅⁻¹ T^{9/16} (log T)^{-5λ/16} ≤ M ≤ C₅ T^{2/3}`. -/
def range118 (lam C₅ M T : ℝ) : Prop :=
  C₅⁻¹ * T ^ ((9 : ℝ) / 16) * Real.log T ^ (-(5 * lam / 16)) ≤ M ∧ M ≤ C₅ * T ^ ((2 : ℝ) / 3)

/-! ### Proposition 1 and Theorem 1 -/

/-- The double sum
`S = ∑_{h=H}^{2H-1} g(h/H) ∑_{m=M}^{M'} G(m/M) e((hT/M) F(m/M))`
(Proposition 1 has `M' = 2M`, Proposition 6 has `M' = 2M - 1`). -/
noncomputable def huxleySum (g G F : ℝ → ℝ) (H M M' T : ℝ) : ℂ :=
  ∑ h ∈ closedRange H (2 * H - 1), ((g ((h : ℝ) / H) : ℝ) : ℂ) *
    ∑ m ∈ closedRange M M', ((G ((m : ℝ) / M) : ℝ) : ℂ) *
      e ((h : ℝ) * T / M * F ((m : ℝ) / M))

/-- **Proposition 1, Case (A)**: in the ranges (1.8), (1.9), subject to
(1.6) for `r = 3` when (1.11), (1.7) when (1.12), and the lower bounds
(1.13), (1.14) on `H`, the bound (1.10) holds. -/
def prop1_caseA (κ lam C₃ C₄ C₅ C₆ B₁ B₂ P₀ : ℝ) (g G : ℝ → ℝ) (F : ℝ → ℝ)
    (H M T : ℝ) : Prop :=
  P₀ ≤ H → P₀ ≤ M → P₀ ≤ T →
  range18 κ lam C₅ M T →
  H ≤ B₁ * M * T ^ (-((23 * κ - 2) / (78 * κ - 7))) *
    Real.log T ^ ((9 * κ - 1) * lam / (78 * κ - 7)) →
  (range111 κ lam C₅ M T → DerivLowerBound3 C₃ F) →
  (range112 κ lam C₅ M T → Cond17 C₄ F) →
  (M ≤ C₅⁻¹ * T ^ ((7 : ℝ) / 16) * Real.log T ^ (lam / (32 * κ)) →
    C₆⁻¹ * T ^ 4 * Real.log T ^ (3 * lam) / M ^ 9 ≤ H) →
  (C₅ * T ^ ((9 : ℝ) / 16) * Real.log T ^ (-(lam / (32 * κ))) ≤ M →
    C₆⁻¹ * M ^ 11 * Real.log T ^ (3 * lam) / T ^ 6 ≤ H) →
  ‖huxleySum g G F H M (2 * M) T‖ ≤
    B₂ * H * (H / M) ^ ((6 * κ - 1) / (100 * κ - 10)) *
      T ^ ((67 * κ - 7) / (200 * κ - 20)) *
      Real.log T ^ (9 / 4 + (39 * κ - 4) * lam / (200 * κ - 20))

/-- **Proposition 1, Case (B)**: if (1.6) holds for `r = 3`, then in the
ranges (1.15), (1.16) the bound (1.17) holds. -/
def prop1_caseB (κ lam C₃ C₅ C₆ B₁ B₂ P₀ : ℝ) (g G : ℝ → ℝ) (F : ℝ → ℝ)
    (H M T : ℝ) : Prop :=
  P₀ ≤ H → P₀ ≤ M → P₀ ≤ T →
  DerivLowerBound3 C₃ F →
  range115 lam C₅ M T →
  H ≤ min (min (B₁ * M ^ ((15 * κ - 1) / (33 * κ - 3)) * T ^ (-(2 * κ / (33 * κ - 3))) *
              Real.log T ^ ((9 * κ - 1) * lam / (33 * κ - 3)))
            (B₁ * M ^ ((3 : ℝ) / 2) * T ^ (-(1 : ℝ) / 2)))
        (C₆ * T ^ 4 * M ^ (-(9 : ℝ)) * Real.log T ^ (3 * lam)) →
  ‖huxleySum g G F H M (2 * M) T‖ ≤
    B₂ * H ^ ((87 * κ - 9) / (80 * κ - 8)) * M ^ ((15 * κ - 1) / (80 * κ - 8)) *
        T ^ ((9 * κ - 1) / (40 * κ - 4)) *
        Real.log T ^ (9 / 4 + (9 * κ - 1) * lam / (80 * κ - 8)) +
      B₂ * H ^ ((107 * κ - 13) / (12 * (9 * κ - 1))) *
        M ^ (-((7 * κ - 1) / (4 * (9 * κ - 1)))) *
        T ^ ((43 * κ - 5) / (12 * (9 * κ - 1))) * Real.log T ^ ((9 + lam) / 4)

/-- **Proposition 1, Case (C)**: if (1.7) holds, then in the ranges (1.18),
(1.19) (with the corrected exponent `(51κ - 5)/(33κ - 3)`) the bound (1.20)
holds. -/
def prop1_caseC (κ lam C₄ C₅ C₆ B₁ B₂ P₀ : ℝ) (g G : ℝ → ℝ) (F : ℝ → ℝ)
    (H M T : ℝ) : Prop :=
  P₀ ≤ H → P₀ ≤ M → P₀ ≤ T →
  Cond17 C₄ F →
  range118 lam C₅ M T →
  H ≤ min (min (B₁ * M ^ ((51 * κ - 5) / (33 * κ - 3)) *
              T ^ (-((20 * κ - 2) / (33 * κ - 3))) *
              Real.log T ^ ((9 * κ - 1) * lam / (33 * κ - 3)))
            (B₁ * M ^ ((1 : ℝ) / 2)))
        (C₆ * M ^ 11 * T ^ (-(6 : ℝ)) * Real.log T ^ (3 * lam)) →
  ‖huxleySum g G F H M (2 * M) T‖ ≤
    B₂ * H ^ ((87 * κ - 9) / (80 * κ - 8)) * M ^ (-((29 * κ - 3) / (80 * κ - 8))) *
        T ^ ((1 : ℝ) / 2) * Real.log T ^ (9 / 4 + (9 * κ - 1) * lam / (80 * κ - 8)) +
      B₂ * H ^ ((107 * κ - 13) / (12 * (9 * κ - 1))) *
        M ^ ((23 * κ - 1) / (12 * (9 * κ - 1))) *
        T ^ ((7 * κ - 1) / (4 * (9 * κ - 1))) * Real.log T ^ ((9 + lam) / 4)

/-- **Proposition 1** (conclusion for given `κ, λ`).  For `C₁, …, C₆ ≥ 1`
and bounded `g, G` of bounded variation on `[1, 2]` there are positive
`B₁, B₂` (and a largeness threshold `P₀`) such that for every `C³` function
`F` satisfying (1.5) for `r = 1, 2, 3` and (1.6) for `r = 1, 2`, Cases
(A), (B), (C) hold. -/
def huxley_prop1_conclusion (κ lam : ℝ) : Prop :=
  ∀ C₁ C₂ C₃ C₄ C₅ C₆ : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 1 ≤ C₃ → 1 ≤ C₄ → 1 ≤ C₅ → 1 ≤ C₆ →
    ∀ (K : ℝ) (g G : ℝ → ℝ), BVBounded K g → BVBounded K G →
      ∃ B₁ B₂ P₀ : ℝ, 0 < B₁ ∧ 0 < B₂ ∧
        ∀ (F : ℝ → ℝ) (H M T : ℝ), DerivConditions C₁ C₂ C₃ F →
          prop1_caseA κ lam C₃ C₄ C₅ C₆ B₁ B₂ P₀ g G F H M T ∧
          prop1_caseB κ lam C₃ C₅ C₆ B₁ B₂ P₀ g G F H M T ∧
          prop1_caseC κ lam C₄ C₅ C₆ B₁ B₂ P₀ g G F H M T

/-- **Proposition 1**: `H(κ, λ)` with `1/4 ≤ κ ≤ 1/3`, `λ ≥ 0` implies the
bounds of Proposition 1. -/
def huxley_prop1 : Prop :=
  ∀ κ lam : ℝ, 1 / 4 ≤ κ → κ ≤ 1 / 3 → 0 ≤ lam → HuxleyHypothesisH κ lam →
    huxley_prop1_conclusion κ lam

/-- **Theorem 1**: Proposition 1 holds unconditionally with `κ = 3/10`,
`λ = 57/140`. -/
def huxley_theorem1 : Prop := huxley_prop1_conclusion ((3 : ℝ) / 10) ((57 : ℝ) / 140)

/-! ### Proposition 2 and Theorem 2 -/

/-- The right-hand side of (1.22)/(1.25):
`B T^{(67κ-7)/(212κ-22)} (log T)^{(450κ-45+(39κ-4)λ)/(212κ-22)}`. -/
noncomputable def bound122 (κ lam B T : ℝ) : ℝ :=
  B * T ^ ((67 * κ - 7) / (212 * κ - 22)) *
    Real.log T ^ ((450 * κ - 45 + (39 * κ - 4) * lam) / (212 * κ - 22))

/-- The right-hand side of (1.23) without the term `B δ M`. -/
noncomputable def bound123 (κ lam B M T : ℝ) : ℝ :=
  B * M ^ ((22 * κ - 2) / (87 * κ - 9)) * T ^ ((18 * κ - 2) / (87 * κ - 9)) *
      Real.log T ^ ((180 * κ - 18 + (9 * κ - 1) * lam) / (87 * κ - 9)) +
    B * M ^ (-((22 * κ - 2) / (107 * κ - 13))) * T ^ ((43 * κ - 5) / (107 * κ - 13)) *
      Real.log T ^ (3 * (9 + lam) * (9 * κ - 1) / (107 * κ - 13))

/-- The right-hand side of (1.24) without the term `B δ M`. -/
noncomputable def bound124 (κ lam B M T : ℝ) : ℝ :=
  B * M ^ (-((22 * κ - 2) / (87 * κ - 9))) * T ^ ((40 * κ - 4) / (87 * κ - 9)) *
      Real.log T ^ ((180 * κ - 18 + (9 * κ - 1) * lam) / (87 * κ - 9)) +
    B * M ^ ((22 * κ - 2) / (107 * κ - 13)) * T ^ ((21 * κ - 3) / (107 * κ - 13)) *
      Real.log T ^ (3 * (9 + lam) * (9 * κ - 1) / (107 * κ - 13))

/-- `R(δ)` of (1.21): the number of integer points `(m, n)` with
`|n - N F(m/M)| ≤ δ`, `M ≤ m ≤ 2M - 1`. -/
noncomputable def closeCount121 (F : ℝ → ℝ) (M N δ : ℝ) : ℕ :=
  closePointCount (fun x => N * F (x / M)) M (2 * M - 1) δ

/-- **Proposition 2** (conclusion for given `κ, λ`).  With `T = MN`:
(A) in the range (1.8), subject to (1.6) for `r = 3` in (1.11) and (1.7) in
(1.12), `R(δ) ≤ B₃ δ M + (1.22)`; (B) if (1.6) holds for `r = 3`, then in
(1.15) `R(δ) ≤ B₃ δ M + (1.23)`; (C) if (1.7) holds, then in (1.18)
`R(δ) ≤ B₃ δ M + (1.24)`. -/
def huxley_prop2_conclusion (κ lam : ℝ) : Prop :=
  ∀ C₁ C₂ C₃ C₄ C₅ : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 1 ≤ C₃ → 1 ≤ C₄ → 1 ≤ C₅ →
    ∃ B₃ P₀ : ℝ, 0 < B₃ ∧
      ∀ (F : ℝ → ℝ) (M N δ : ℝ), DerivConditions C₁ C₂ C₃ F →
        P₀ ≤ M → P₀ ≤ N → 0 ≤ δ → δ ≤ 1 / 2 →
        (range18 κ lam C₅ M (M * N) →
          (range111 κ lam C₅ M (M * N) → DerivLowerBound3 C₃ F) →
          (range112 κ lam C₅ M (M * N) → Cond17 C₄ F) →
          (closeCount121 F M N δ : ℝ) ≤ B₃ * δ * M + bound122 κ lam B₃ (M * N)) ∧
        (DerivLowerBound3 C₃ F → range115 lam C₅ M (M * N) →
          (closeCount121 F M N δ : ℝ) ≤ B₃ * δ * M + bound123 κ lam B₃ M (M * N)) ∧
        (Cond17 C₄ F → range118 lam C₅ M (M * N) →
          (closeCount121 F M N δ : ℝ) ≤ B₃ * δ * M + bound124 κ lam B₃ M (M * N))

/-- **Proposition 2**: `H(κ, λ)` with `1/4 ≤ κ ≤ 1/3`, `λ ≥ 0` implies the
bounds of Proposition 2. -/
def huxley_prop2 : Prop :=
  ∀ κ lam : ℝ, 1 / 4 ≤ κ → κ ≤ 1 / 3 → 0 ≤ lam → HuxleyHypothesisH κ lam →
    huxley_prop2_conclusion κ lam

/-- **Theorem 2**: Proposition 2 holds unconditionally with `κ = 3/10`,
`λ = 57/140`. -/
def huxley_theorem2 : Prop := huxley_prop2_conclusion ((3 : ℝ) / 10) ((57 : ℝ) / 140)

/-! ### Proposition 3, its Corollary, and Theorem 3 -/

/-- The right-hand side of (1.26). -/
noncomputable def bound126 (κ lam B M T : ℝ) : ℝ :=
  B * M ^ ((22 * κ - 2) / (87 * κ - 9)) * T ^ ((18 * κ - 2) / (87 * κ - 9)) *
      Real.log T ^ ((180 * κ - 18 + (9 * κ - 1) * lam) / (87 * κ - 9)) +
    B * M ^ (-(1 : ℝ) / 5) * T ^ ((2 : ℝ) / 5) *
      Real.log T ^ (3 * (9 + lam) * (9 * κ - 1) / (110 * κ - 10))

/-- The right-hand side of (1.27). -/
noncomputable def bound127 (κ lam B M T : ℝ) : ℝ :=
  B * M ^ (-((22 * κ - 2) / (87 * κ - 9))) * T ^ ((40 * κ - 4) / (87 * κ - 9)) *
      Real.log T ^ ((180 * κ - 18 + (9 * κ - 1) * lam) / (87 * κ - 9)) +
    B * M ^ ((1 : ℝ) / 5) * T ^ ((1 : ℝ) / 5) *
      Real.log T ^ (3 * (9 + lam) * (9 * κ - 1) / (110 * κ - 10))

/-- The rounding error sum `R = ∑_{m=M}^{M₂} ρ(N F(m/M))` of Proposition 3. -/
noncomputable def roundingSum (F : ℝ → ℝ) (N M : ℝ) (M₂ : ℕ) : ℝ :=
  ∑ m ∈ closedRange M M₂, rowOfTeeth (N * F ((m : ℝ) / M))

/-- The expression (1.28):
`∑_{m=M}^{M₂} [N F(m/M)] - ∫_{M-1/2}^{M₂+1/2} (N F(x/M) - 1/2) dx`. -/
noncomputable def floorSumMinusIntegral (F : ℝ → ℝ) (N M : ℝ) (M₂ : ℕ) : ℝ :=
  (∑ m ∈ closedRange M M₂, ((⌊N * F ((m : ℝ) / M)⌋ : ℤ) : ℝ)) -
    ∫ x in (M - 1 / 2)..((M₂ : ℝ) + 1 / 2), (N * F (x / M) - 1 / 2)

/-- The extra hypothesis of the Corollary to Proposition 3: the bounds
(1.5) for `r = 1, 2` also hold on the wider range
`1 - 1/(2M) ≤ x ≤ 2 + 1/(2M)` (where the paper only asks `F` to have two
continuous derivatives; see the module docstring). -/
def WiderRangeBounds (C₁ C₂ : ℝ) (F : ℝ → ℝ) (M : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (1 - 1 / (2 * M)) (2 + 1 / (2 * M)),
    |deriv F x| ≤ C₁ ∧ |iteratedDeriv 2 F x| ≤ C₂

/-- The three cases (A), (B), (C) of Proposition 3 for a quantity
`Φ F N M M₂` (the rounding error sum `R`, or the expression (1.28)), under
the conditions of Proposition 2 on `F`, the extra hypothesis `extra F M`,
`M, N` large, `T = MN`, and `M ≤ M₂ ≤ 2M - 1`. -/
def prop3Bounds (κ lam C₁ C₂ C₃ C₄ C₅ B₄ P₀ : ℝ) (extra : (ℝ → ℝ) → ℝ → Prop)
    (Φ : (ℝ → ℝ) → ℝ → ℝ → ℕ → ℝ) : Prop :=
  ∀ (F : ℝ → ℝ) (M N : ℝ) (M₂ : ℕ), DerivConditions C₁ C₂ C₃ F → extra F M →
    P₀ ≤ M → P₀ ≤ N → M ≤ M₂ → (M₂ : ℝ) ≤ 2 * M - 1 →
    (range18 κ lam C₅ M (M * N) →
      (range111 κ lam C₅ M (M * N) → DerivLowerBound3 C₃ F) →
      (range112 κ lam C₅ M (M * N) → Cond17 C₄ F) →
      |Φ F N M M₂| ≤ bound122 κ lam B₄ (M * N)) ∧
    (DerivLowerBound3 C₃ F → range115 lam C₅ M (M * N) →
      |Φ F N M M₂| ≤ bound126 κ lam B₄ M (M * N)) ∧
    (Cond17 C₄ F → range118 lam C₅ M (M * N) →
      |Φ F N M M₂| ≤ bound127 κ lam B₄ M (M * N))

/-- **Proposition 3** (conclusion for given `κ, λ`): the rounding error sum
`R = ∑_{m=M}^{M₂} ρ(N F(m/M))` satisfies (1.25) in Case (A), (1.26) in Case
(B) and (1.27) in Case (C). -/
def huxley_prop3_conclusion (κ lam : ℝ) : Prop :=
  ∀ C₁ C₂ C₃ C₄ C₅ : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 1 ≤ C₃ → 1 ≤ C₄ → 1 ≤ C₅ →
    ∃ B₄ P₀ : ℝ, 0 < B₄ ∧
      prop3Bounds κ lam C₁ C₂ C₃ C₄ C₅ B₄ P₀ (fun _ _ => True) roundingSum

/-- **Corollary to Proposition 3** (conclusion for given `κ, λ`): if `F` is
defined with two continuous derivatives on `1 - 1/(2M) ≤ x ≤ 2 + 1/(2M)`
(here: with the bounds (1.5), `r = 1, 2`, on that range), the expression
(1.28) satisfies the bounds of Proposition 3 with a possibly larger `B₄`. -/
def huxley_prop3_corollary_conclusion (κ lam : ℝ) : Prop :=
  ∀ C₁ C₂ C₃ C₄ C₅ : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 1 ≤ C₃ → 1 ≤ C₄ → 1 ≤ C₅ →
    ∃ B₄ P₀ : ℝ, 0 < B₄ ∧
      prop3Bounds κ lam C₁ C₂ C₃ C₄ C₅ B₄ P₀ (WiderRangeBounds C₁ C₂) floorSumMinusIntegral

/-- **Proposition 3** (with its Corollary): `H(κ, λ)` with
`1/4 ≤ κ ≤ 1/3`, `λ ≥ 0` implies both conclusions. -/
def huxley_prop3 : Prop :=
  ∀ κ lam : ℝ, 1 / 4 ≤ κ → κ ≤ 1 / 3 → 0 ≤ lam → HuxleyHypothesisH κ lam →
    huxley_prop3_conclusion κ lam ∧ huxley_prop3_corollary_conclusion κ lam

/-- **Theorem 3**: Proposition 3 and its Corollary hold unconditionally with
`κ = 3/10`, `λ = 57/140`. -/
def huxley_theorem3 : Prop :=
  huxley_prop3_conclusion ((3 : ℝ) / 10) ((57 : ℝ) / 140) ∧
    huxley_prop3_corollary_conclusion ((3 : ℝ) / 10) ((57 : ℝ) / 140)

/-! ### Proposition 4 and Theorem 4 -/

/-- **Proposition 4** (conclusion for given `κ, λ`).  Under the conditions
`Prop4Conditions` on `F`, with `T = MN`, the bound (1.25) holds for the
rounding error sum `R` (and for the expression (1.28), under the wider-range
hypothesis of the Corollary) in the range (1.30)
`M ≤ C₅ T^{(123κ-13)/(212κ-22)} (log T)^A`, for some exponent `A`
depending on `κ, λ`. -/
def huxley_prop4_conclusion (κ lam : ℝ) : Prop :=
  ∀ C₀ C₁ C₂ C₃ C₄ C₅ : ℝ, 1 ≤ C₀ → 1 ≤ C₁ → 1 ≤ C₂ → 1 ≤ C₃ → 1 ≤ C₄ → 1 ≤ C₅ →
    ∃ A B₄ P₀ : ℝ, 0 < B₄ ∧
      ∀ (F : ℝ → ℝ) (M N : ℝ) (M₂ : ℕ), Prop4Conditions C₀ C₁ C₂ C₃ C₄ F →
        P₀ ≤ M → P₀ ≤ N → M ≤ M₂ → (M₂ : ℝ) ≤ 2 * M - 1 →
        M ≤ C₅ * (M * N) ^ ((123 * κ - 13) / (212 * κ - 22)) * Real.log (M * N) ^ A →
        |roundingSum F N M M₂| ≤ bound122 κ lam B₄ (M * N) ∧
          (WiderRangeBounds C₁ C₂ F M →
            |floorSumMinusIntegral F N M M₂| ≤ bound122 κ lam B₄ (M * N))

/-- **Proposition 4**: `H(κ, λ)` with `1/4 ≤ κ ≤ 1/3`, `λ ≥ 0` implies the
conclusion of Proposition 4. -/
def huxley_prop4 : Prop :=
  ∀ κ lam : ℝ, 1 / 4 ≤ κ → κ ≤ 1 / 3 → 0 ≤ lam → HuxleyHypothesisH κ lam →
    huxley_prop4_conclusion κ lam

/-- **Theorem 4**: Proposition 4 holds unconditionally with `κ = 3/10`,
`λ = 57/140`. -/
def huxley_theorem4 : Prop := huxley_prop4_conclusion ((3 : ℝ) / 10) ((57 : ℝ) / 140)

/-! ### Proposition 5 and Theorem 5: lattice points in a convex domain -/

/-- A closed convex curve of Huxley's class `C³`, given by its radius of
curvature `ρ` as a function of the tangent angle `ψ ∈ [0, 2π]`: there is a
partition `0 = ψ 0 < ψ 1 < … < ψ k = 2π` into `k` pieces, on the `i`-th
piece `ρ` agrees with a globally `C¹` function `ρs i` that is positive on the
closed piece, and the curve closes up.  The boundary is
`ψ ↦ (∫₀^ψ ρ cos, ∫₀^ψ ρ sin)`. -/
structure SmoothConvexCurve where
  /-- The number of pieces. -/
  k : ℕ
  /-- The tangent angles at which the pieces meet. -/
  ψ : Fin (k + 1) → ℝ
  /-- The radius of curvature as a function of the tangent angle. -/
  ρ : ℝ → ℝ
  /-- The `C¹` functions giving `ρ` on each piece. -/
  ρs : Fin k → ℝ → ℝ
  ψ_zero : ψ 0 = 0
  ψ_last : ψ (Fin.last k) = 2 * Real.pi
  ψ_strictMono : StrictMono ψ
  ρ_piece : ∀ i : Fin k, ∀ θ ∈ Set.Ico (ψ i.castSucc) (ψ i.succ), ρ θ = ρs i θ
  ρs_smooth : ∀ i : Fin k, ContDiff ℝ 1 (ρs i)
  ρs_pos : ∀ i : Fin k, ∀ θ ∈ Set.Icc (ψ i.castSucc) (ψ i.succ), 0 < ρs i θ
  closed_x : ∫ θ in (0 : ℝ)..(2 * Real.pi), ρ θ * Real.cos θ = 0
  closed_y : ∫ θ in (0 : ℝ)..(2 * Real.pi), ρ θ * Real.sin θ = 0

namespace SmoothConvexCurve

/-- The closed `i`-th piece `[ψ i, ψ (i+1)]` of tangent angles. -/
def piece (c : SmoothConvexCurve) (i : Fin c.k) : Set ℝ :=
  Set.Icc (c.ψ i.castSucc) (c.ψ i.succ)

/-- The boundary point with tangent angle `ψ`. -/
noncomputable def point (c : SmoothConvexCurve) (ψ : ℝ) : ℝ × ℝ :=
  (∫ θ in (0 : ℝ)..ψ, c.ρ θ * Real.cos θ, ∫ θ in (0 : ℝ)..ψ, c.ρ θ * Real.sin θ)

/-- The closed convex domain `Ω` bounded by the curve. -/
noncomputable def region (c : SmoothConvexCurve) : Set (ℝ × ℝ) :=
  convexHull ℝ (c.point '' Set.Icc (0 : ℝ) (2 * Real.pi))

/-- The area `A` of `Ω`. -/
noncomputable def area (c : SmoothConvexCurve) : ℝ :=
  (MeasureTheory.volume c.region).toReal

end SmoothConvexCurve

/-- The number of integer points `(m, n)` in the image of `Ω` under the
rigid motion `p ↦ M R_θ (p₁, σ p₂) + (a, b)` (dilation by `M`, rotation by
`θ`, reflection when `σ = -1`, translation by `(a, b)`). -/
noncomputable def latticeCountIn (Ω : Set (ℝ × ℝ)) (M θ σ a b : ℝ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | ∃ q ∈ Ω,
    M * (q.1 * Real.cos θ - σ * q.2 * Real.sin θ) + a = (p.1 : ℝ) ∧
      M * (q.1 * Real.sin θ + σ * q.2 * Real.cos θ) + b = (p.2 : ℝ)}

/-- The error term of (1.31) without the factor `I`:
`M^{(67κ-7)/(106κ-11)} (log M)^{(450κ-45+(39κ-4)λ)/(212κ-22)}`. -/
noncomputable def bound131 (κ lam M : ℝ) : ℝ :=
  M ^ ((67 * κ - 7) / (106 * κ - 11)) *
    Real.log M ^ ((450 * κ - 45 + (39 * κ - 4) * lam) / (212 * κ - 22))

/-- **Proposition 5** (conclusion for given `κ, λ`).  For every convex
domain `Ω` of class `C³` (`SmoothConvexCurve`) of area `A`, for `M`
sufficiently large and every isometric embedding of `MΩ`, the number of
integer points in `MΩ` is `A M² + O(I · (1.31))` with `I` depending only
on the curve (the constant and `I` are merged into `C`).  Moreover, for
curves with `k` pieces on each of which `ρ` is monotone with
`ρ₀ ≤ ρ ≤ ρ_i`, the bound holds with `I = ∑ ρ_i^{(67κ-7)/(106κ-11)}` and a
constant depending only on `κ, λ` and `k`, for `M` large in terms of
`1/ρ₀`. -/
def huxley_prop5_conclusion (κ lam : ℝ) : Prop :=
  (∀ c : SmoothConvexCurve, ∃ C M₀ : ℝ,
    ∀ M θ σ a b : ℝ, M₀ ≤ M → (σ = 1 ∨ σ = -1) →
      |(latticeCountIn c.region M θ σ a b : ℝ) - c.area * M ^ 2| ≤ C * bound131 κ lam M) ∧
  (∀ k : ℕ, ∃ C : ℝ, ∀ ρ₀ : ℝ, 0 < ρ₀ → ∃ M₀ : ℝ,
    ∀ (c : SmoothConvexCurve) (ρi : Fin c.k → ℝ), c.k = k →
      (∀ i : Fin c.k, MonotoneOn (c.ρs i) (c.piece i) ∨ AntitoneOn (c.ρs i) (c.piece i)) →
      (∀ i : Fin c.k, ∀ θ ∈ c.piece i, ρ₀ ≤ c.ρs i θ ∧ c.ρs i θ ≤ ρi i) →
      ∀ M θ σ a b : ℝ, M₀ ≤ M → (σ = 1 ∨ σ = -1) →
        |(latticeCountIn c.region M θ σ a b : ℝ) - c.area * M ^ 2| ≤
          C * (∑ i : Fin c.k, ρi i ^ ((67 * κ - 7) / (106 * κ - 11))) * bound131 κ lam M)

/-- **Proposition 5**: `H(κ, λ)` with `1/4 ≤ κ ≤ 1/3`, `λ ≥ 0` implies the
conclusion of Proposition 5. -/
def huxley_prop5 : Prop :=
  ∀ κ lam : ℝ, 1 / 4 ≤ κ → κ ≤ 1 / 3 → 0 ≤ lam → HuxleyHypothesisH κ lam →
    huxley_prop5_conclusion κ lam

/-- **Theorem 5**: Proposition 5 holds unconditionally with `κ = 3/10`,
`λ = 57/140`; this is (1.1) with `K = 131/208`, `Λ = 18627/8320` for
convex `C³` curves. -/
def huxley_theorem5 : Prop := huxley_prop5_conclusion ((3 : ℝ) / 10) ((57 : ℝ) / 140)

/-! ### The headline bounds of §1: circle and divisor problems -/

/-- **§1, the Gauss circle problem**: `E(x) = P(x) - π x ≪ x^{131/416} (log x)^{18627/8320}`
(the case `K = 131/208`, `Λ = 18627/8320` of (1.1) for the unit circle,
`x = M²`). -/
def huxley2003_circleBound : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |circleError x| ≤ C * x ^ ((131 : ℝ) / 416) * Real.log x ^ ((18627 : ℝ) / 8320)

/-- `∑_{n ≤ T} d(n)`, the summatory function of the divisor function. -/
noncomputable def divisorSumNat (T : ℝ) : ℕ := ∑ n ∈ upTo T, (Nat.divisors n).card

/-- **§1, the Dirichlet divisor problem**:
`∑_{n ≤ T} d(n) = T log T + (2γ - 1) T + O(T^{131/416} (log T)^{18627/8320 + 1})`. -/
def huxley2003_divisorBound : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    |(divisorSumNat T : ℝ) - (T * Real.log T + (2 * Real.eulerMascheroniConstant - 1) * T)| ≤
      C * T ^ ((131 : ℝ) / 416) * Real.log T ^ ((18627 : ℝ) / 8320 + 1)

/-! ### Proposition 6 and Theorem 6: a family of sums -/

/-- `∂₁^r F(x, y)`, the `r`-th partial derivative in `x`. -/
noncomputable def pd1 (r : ℕ) (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv r (fun t => F t y) x

/-- `∂₂ ∂₁^r F(x, y)`. -/
noncomputable def pd21 (r : ℕ) (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => iteratedDeriv r (fun t => F t s) x) y

/-- The basic conditions of Proposition 6 on `F(x, y)`, `1 ≤ x ≤ 2`,
`0 ≤ y ≤ 1`: `F` is `C⁴` in `x`, `F₁` and `F₁₁` are `C²` in `(x, y)`,
`|∂₁^r F| ≤ C₁` for `r = 1, …, 4`, (1.32) for `r = 1, 2`, and (1.33) for
`r = 1`. -/
def Prop6Conditions (C₁ C₂ C₃ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  (∀ y : ℝ, ContDiff ℝ 4 (fun t => F t y)) ∧
    ContDiff ℝ 2 (fun p : ℝ × ℝ => pd1 1 F p.1 p.2) ∧
    ContDiff ℝ 2 (fun p : ℝ × ℝ => pd1 2 F p.1 p.2) ∧
    ∀ x ∈ Set.Icc (1 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |pd1 1 F x y| ≤ C₁ ∧ |pd1 2 F x y| ≤ C₁ ∧ |pd1 3 F x y| ≤ C₁ ∧ |pd1 4 F x y| ≤ C₁ ∧
        1 / C₂ ≤ |pd1 1 F x y| ∧ 1 / C₂ ≤ |pd1 2 F x y| ∧
        1 / C₃ ≤ |pd1 2 F x y * pd21 2 F x y - pd21 1 F x y * pd1 3 F x y|

/-- (1.32) for `r = 3`: `|∂₁³ F| ≥ 1/C₂`. -/
def Cond132three (C₂ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (1 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 1, 1 / C₂ ≤ |pd1 3 F x y|

/-- (1.33) for `r = 2`: `|(∂₁³F)(∂₂∂₁³F) - (∂₂∂₁²F)(∂₁⁴F)| ≥ 1/C₃`. -/
def Cond133two (C₃ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (1 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    1 / C₃ ≤ |pd1 3 F x y * pd21 3 F x y - pd21 2 F x y * pd1 4 F x y|

/-- (1.34): `|F₁ F₁₁₁ - 3 F₁₁²| ≥ 1/C₄`. -/
def Cond134 (C₄ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (1 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 1,
    1 / C₄ ≤ |pd1 1 F x y * pd1 3 F x y - 3 * pd1 2 F x y ^ 2|

/-- The determinant of the `3 × 3` matrix with rows `(a, b, c)`, `(d, e, f)`,
`(g, h, i)`. -/
def det3 (a b c d e f g h i : ℝ) : ℝ :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- The determinant of (1.35), with rows
`(3F₁₁² + 4F₁F₁₁₁, 3F₁F₁₁, F₁²)`, `(F₁₁₁₁, F₁₁₁, F₁₁)`, `(F₁₁₁₂, F₁₁₂, F₁₂)`. -/
noncomputable def det135 (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  det3 (3 * pd1 2 F x y ^ 2 + 4 * pd1 1 F x y * pd1 3 F x y) (3 * pd1 1 F x y * pd1 2 F x y)
      (pd1 1 F x y ^ 2)
    (pd1 4 F x y) (pd1 3 F x y) (pd1 2 F x y)
    (pd21 3 F x y) (pd21 2 F x y) (pd21 1 F x y)

/-- (1.35): the determinant is at least `1/C₅` in absolute value. -/
def Cond135 (C₅ : ℝ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (1 : ℝ) 2, ∀ y ∈ Set.Icc (0 : ℝ) 1, 1 / C₅ ≤ |det135 F x y|

/-- The points `y₁ < … < y_I` of Proposition 6: in `[0, 1]`, strictly
increasing, with consecutive gaps at least `1/(C₀ I)`. -/
def SpacedPoints (C₀ : ℝ) {I : ℕ} (y : Fin I → ℝ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ StrictMono y ∧
    ∀ i j : Fin I, i < j → 1 / (C₀ * (I : ℝ)) ≤ y j - y i

/-- The sum `S_i = ∑_{h=H}^{2H-1} g(h/H) ∑_{m=M}^{2M-1} G_i(m/M) e((hT/M) F(m/M, y_i))`. -/
noncomputable def familySum (g : ℝ → ℝ) {I : ℕ} (Gs : Fin I → ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (y : Fin I → ℝ) (H M T : ℝ) (i : Fin I) : ℂ :=
  huxleySum g (Gs i) (fun x => F x (y i)) H M (2 * M - 1) T

/-- `Σ = ∑_{i=1}^{I} |S_i|²`. -/
noncomputable def familySumSq (g : ℝ → ℝ) {I : ℕ} (Gs : Fin I → ℝ → ℝ) (F : ℝ → ℝ → ℝ)
    (y : Fin I → ℝ) (H M T : ℝ) : ℝ :=
  ∑ i : Fin I, ‖familySum g Gs F y H M T i‖ ^ 2

/-- **Proposition 6, Case (A)**: if either `M ≤ C₆ √T` with (1.32) for `r = 3`
and (1.33) for `r = 2`, or `M ≥ C₆⁻¹ √T` with (1.34) and (1.35), then in the
ranges (1.36), (1.37) the bound (1.38) holds. -/
def prop6_caseA (κ lam C₂ C₃ C₄ C₅ C₆ C₇ B₁ B₂ : ℝ) {I : ℕ} (F : ℝ → ℝ → ℝ)
    (Sig H M T : ℝ) : Prop :=
  ((M ≤ C₆ * Real.sqrt T ∧ Cond132three C₂ F ∧ Cond133two C₃ F) ∨
      (C₆⁻¹ * Real.sqrt T ≤ M ∧ Cond134 C₄ F ∧ Cond135 C₅ F)) →
  C₆⁻¹ * ((I : ℝ) * Real.log T ^ lam) ^ (45 * κ - 4) * T ^ (67 * κ - 6) ≤ M ^ (156 * κ - 14) →
  M ^ (156 * κ - 14) ≤ C₆ * ((I : ℝ) * Real.log T ^ lam) ^ (-(45 * κ - 4)) * T ^ (89 * κ - 8) →
  C₇⁻¹ * (I : ℝ) ^ 3 * (T ^ 4 / M ^ 9 + M ^ 11 / T ^ 6) * Real.log T ^ (3 * lam) ≤ H →
  H ≤ B₁ * ((I : ℝ) * Real.log T ^ lam) ^ ((9 * κ - 1) / (78 * κ - 7)) * M *
    T ^ (-((23 * κ - 2) / (78 * κ - 7))) →
  Sig ≤ B₂ * H ^ 2 * (H / M) ^ ((6 * κ - 1) / (50 * κ - 5)) *
    (I : ℝ) ^ ((89 * κ - 9) / (100 * κ - 10)) * T ^ ((67 * κ - 7) / (100 * κ - 10)) *
    Real.log T ^ (9 / 2 + (39 * κ - 4) * lam / (100 * κ - 10))

/-- **Proposition 6, Case (B)**: if (1.32) for `r = 3` and (1.33) for `r = 2`
hold, then in the ranges (1.39), (1.40) the bound (1.41) holds. -/
def prop6_caseB (κ lam C₂ C₃ C₆ C₇ B₁ B₂ : ℝ) {I : ℕ} (F : ℝ → ℝ → ℝ)
    (Sig H M T : ℝ) : Prop :=
  Cond132three C₂ F → Cond133two C₃ F →
  C₆⁻¹ * T ^ ((1 : ℝ) / 3) ≤ M → M ≤ C₆ * T ^ ((1 : ℝ) / 2) →
  H ≤ min (min (C₇ * (I : ℝ) ^ 3 * T ^ 4 * Real.log T ^ (3 * lam) / M ^ 9)
              (B₁ * (((I : ℝ) * Real.log T ^ lam) ^ (9 * κ - 1) * M ^ (15 * κ - 1) /
                T ^ (2 * κ)) ^ (1 / (33 * κ - 3))))
        (min (B₁ * M ^ ((3 : ℝ) / 2) * T ^ (-(1 : ℝ) / 2))
          (B₁ * M ^ ((54 * κ - 4) / (45 * κ - 3)) * T ^ (-(1 : ℝ) / 3))) →
  Sig ≤ B₂ * H ^ ((87 * κ - 9) / (40 * κ - 4)) * (I : ℝ) ^ ((29 * κ - 3) / (40 * κ - 4)) *
        M ^ ((15 * κ - 1) / (40 * κ - 4)) * T ^ ((9 * κ - 1) / (20 * κ - 2)) *
        Real.log T ^ (9 / 2 + (9 * κ - 1) * lam / (40 * κ - 4)) +
      B₂ * H ^ ((107 * κ - 13) / (6 * (9 * κ - 1))) * (I : ℝ) *
        M ^ (-((7 * κ - 1) / (2 * (9 * κ - 1)))) * T ^ ((43 * κ - 5) / (6 * (9 * κ - 1))) *
        Real.log T ^ ((9 + lam) / 2) +
      B₂ * H ^ ((111 * κ - 9) / (48 * κ - 4)) * (I : ℝ) *
        M ^ (-((13 * κ - 1) / (24 * κ - 2))) * T ^ ((37 * κ - 3) / (48 * κ - 4)) *
        Real.log T ^ ((9 + lam) / 2)

/-- **Proposition 6, Case (C)**: if (1.34) and (1.35) hold, then in the
ranges (1.42), (1.43) the bound (1.44) holds. -/
def prop6_caseC (κ lam C₄ C₅ C₆ C₇ B₁ B₂ : ℝ) {I : ℕ} (F : ℝ → ℝ → ℝ)
    (Sig H M T : ℝ) : Prop :=
  Cond134 C₄ F → Cond135 C₅ F →
  C₆⁻¹ * T ^ ((1 : ℝ) / 2) ≤ M → M ≤ C₆ * T ^ ((2 : ℝ) / 3) →
  H ≤ min (min (C₇ * (I : ℝ) ^ 3 * M ^ 11 * Real.log T ^ (3 * lam) / T ^ 6)
              (B₁ * (((I : ℝ) * Real.log T ^ lam) ^ (9 * κ - 1) * M ^ (51 * κ - 5) /
                T ^ (20 * κ - 2)) ^ (1 / (33 * κ - 3))))
        (min (B₁ * M ^ ((1 : ℝ) / 2))
          (B₁ * M ^ ((54 * κ - 4) / (45 * κ - 3)) * T ^ (-(1 : ℝ) / 3))) →
  Sig ≤ B₂ * H ^ ((87 * κ - 9) / (40 * κ - 4)) * (I : ℝ) ^ ((29 * κ - 3) / (40 * κ - 4)) *
        M ^ (-((29 * κ - 3) / (40 * κ - 4))) * T *
        Real.log T ^ (9 / 2 + (9 * κ - 1) * lam / (40 * κ - 4)) +
      B₂ * H ^ ((107 * κ - 13) / (6 * (9 * κ - 1))) * (I : ℝ) *
        M ^ ((23 * κ - 1) / (6 * (9 * κ - 1))) * T ^ ((7 * κ - 1) / (2 * (9 * κ - 1))) *
        Real.log T ^ ((9 + lam) / 2) +
      B₂ * H ^ ((111 * κ - 9) / (48 * κ - 4)) * (I : ℝ) *
        M ^ (-((13 * κ - 1) / (24 * κ - 2))) * T ^ ((37 * κ - 3) / (48 * κ - 4)) *
        Real.log T ^ ((9 + lam) / 2)

/-- **Proposition 6** (conclusion for given `κ, λ`).  For `C₀, …, C₇ ≥ 1`
and a uniform bound `K` for `g` and the `G_i`, there are positive `B₁, B₂`
(and a threshold `P₀`) such that for every `F` satisfying
`Prop6Conditions`, every family of spaced points `y₁ < … < y_I`, and large
`H, M, T`, Cases (A), (B), (C) hold for `Σ = ∑ |S_i|²`. -/
def huxley_prop6_conclusion (κ lam : ℝ) : Prop :=
  ∀ C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇ : ℝ, 1 ≤ C₀ → 1 ≤ C₁ → 1 ≤ C₂ → 1 ≤ C₃ → 1 ≤ C₄ → 1 ≤ C₅ →
    1 ≤ C₆ → 1 ≤ C₇ → ∀ K : ℝ, 0 < K →
      ∃ B₁ B₂ P₀ : ℝ, 0 < B₁ ∧ 0 < B₂ ∧
        ∀ (I : ℕ) (F : ℝ → ℝ → ℝ) (y : Fin I → ℝ) (g : ℝ → ℝ) (Gs : Fin I → ℝ → ℝ)
          (H M T : ℝ), Prop6Conditions C₁ C₂ C₃ F → SpacedPoints C₀ y →
          BVBounded K g → (∀ i, BVBounded K (Gs i)) → 1 ≤ I →
          P₀ ≤ H → P₀ ≤ M → P₀ ≤ T →
          prop6_caseA κ lam C₂ C₃ C₄ C₅ C₆ C₇ B₁ B₂ (I := I) F
              (familySumSq g Gs F y H M T) H M T ∧
            prop6_caseB κ lam C₂ C₃ C₆ C₇ B₁ B₂ (I := I) F
              (familySumSq g Gs F y H M T) H M T ∧
            prop6_caseC κ lam C₄ C₅ C₆ C₇ B₁ B₂ (I := I) F
              (familySumSq g Gs F y H M T) H M T

/-- **Proposition 6**: `H(κ, λ)` with `1/4 ≤ κ ≤ 1/3`, `λ ≥ 0` implies the
conclusion of Proposition 6. -/
def huxley_prop6 : Prop :=
  ∀ κ lam : ℝ, 1 / 4 ≤ κ → κ ≤ 1 / 3 → 0 ≤ lam → HuxleyHypothesisH κ lam →
    huxley_prop6_conclusion κ lam

/-- **Theorem 6**: Proposition 6 holds unconditionally with `κ = 3/10`,
`λ = 57/140`. -/
def huxley_theorem6 : Prop := huxley_prop6_conclusion ((3 : ℝ) / 10) ((57 : ℝ) / 140)

/-! ### §2: Farey arcs and the counting lemmas 2.3–2.5

The phase is `f(x) = (T/M) F(x/M)`, the inner phase of the sum `S` of
Proposition 1 for `h = 1` (so `f' ≍ T/M²` and `f'' ≍ T/M³`, as (2.2) and the
remark after (2.10) require); `[M, 2M]` is cut into short intervals of
length `N`, and `R` is the least positive integer with (2.1)–(2.2).  The
parameters must satisfy (2.3)–(2.5). -/

/-- The phase `f(x) = (T/M) F(x/M)`. -/
noncomputable def phase (F : ℝ → ℝ) (T M x : ℝ) : ℝ := T / M * F (x / M)

/-- The `j`-th short interval `[M + jN, M + (j+1)N]`. -/
def shortInterval (M N : ℝ) (j : ℕ) : Set ℝ := Set.Icc (M + j * N) (M + (j + 1) * N)

/-- The index set of the short intervals of length `N` contained in `[M, 2M]`:
`j = 0, …, ⌊M/N⌋ - 1` (a final shorter piece of `[M, 2M]`, where `M/N` is not
an integer, is discarded; this can only lower the counts bounded below). -/
noncomputable def shortIndices (M N : ℝ) : Finset ℕ := Finset.range ⌊M / N⌋₊

/-- `a/q` is the Farey label of the `j`-th short interval: a reduced rational
value of `f'` on the interval with `q ≥ R`, and `q` minimal with this
property. -/
def IsFareyLabel (f : ℝ → ℝ) (M N R : ℝ) (j : ℕ) (a : ℤ) (q : ℕ) : Prop :=
  R ≤ q ∧ Nat.Coprime a.natAbs q ∧
    (∃ x ∈ shortInterval M N j, deriv f x = (a : ℝ) / (q : ℝ)) ∧
    ∀ (a' : ℤ) (q' : ℕ), R ≤ q' → q' < q → Nat.Coprime a'.natAbs q' →
      ∀ x ∈ shortInterval M N j, deriv f x ≠ (a' : ℝ) / (q' : ℝ)

/-- The parameter conditions (2.1)–(2.5) of §2 for the phase `f` with
constant `C₂` (from (1.6), `r = 2`): `1/(N R²) ≤ min |f''|`,
`(R-1)² N T < C₂ M³ ≤ R² N T`, `64 C₂ H ≤ N ≤ M/10`, `2 C₂ √H + 1 ≤ R ≤ H`,
`H N² ≤ M R²`. -/
def ArcParameters (C₂ : ℝ) (f : ℝ → ℝ) (M T H N : ℝ) (R : ℕ) : Prop :=
  (∀ x ∈ Set.Icc M (2 * M), 1 / (N * (R : ℝ) ^ 2) ≤ |iteratedDeriv 2 f x|) ∧
    ((R : ℝ) - 1) ^ 2 * N * T < C₂ * M ^ 3 ∧ C₂ * M ^ 3 ≤ (R : ℝ) ^ 2 * N * T ∧
    64 * C₂ * H ≤ N ∧ N ≤ M / 10 ∧
    2 * C₂ * Real.sqrt H + 1 ≤ R ∧ (R : ℝ) ≤ H ∧
    H * N ^ 2 ≤ M * (R : ℝ) ^ 2

open Classical in
/-- The number of short intervals whose Farey label has `Q ≤ q ≤ 2Q`. -/
noncomputable def fareyArcCount (f : ℝ → ℝ) (M N R Q : ℝ) : ℕ :=
  ((shortIndices M N).filter fun j =>
    ∃ (a : ℤ) (q : ℕ), Q ≤ q ∧ (q : ℝ) ≤ 2 * Q ∧ IsFareyLabel f M N R j a q).card

/-- **Lemma 2.3** (counting Farey arcs).  Under (1.5)/(1.6) for `F` and
(2.1)–(2.5), for `Q ≥ R/2` the number of short intervals with label
`Q ≤ q ≤ 2Q` is `O(M R² / (N Q²))`. -/
def huxley_lemma23 : Prop :=
  ∀ C₁ C₂ C₃ : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 1 ≤ C₃ →
    ∃ C : ℝ, ∀ (F : ℝ → ℝ) (T M H N Q : ℝ) (R : ℕ), DerivConditions C₁ C₂ C₃ F →
      1 ≤ T → ArcParameters C₂ (phase F T M) M T H N R → (R : ℝ) / 2 ≤ Q →
      (fareyArcCount (phase F T M) M N R Q : ℝ) ≤ C * (M * (R : ℝ) ^ 2 / (N * Q ^ 2))

/-- `x` lies in a bad interval (2.9): `|f'(x) - c/k| ≤ η/(K Q')` for some
rational `c/k` with `k ≤ Q'`. -/
def IsBadPoint (f : ℝ → ℝ) (η Q' K x : ℝ) : Prop :=
  ∃ (c : ℤ) (k : ℕ), 1 ≤ k ∧ (k : ℝ) ≤ Q' ∧ |deriv f x - (c : ℝ) / (k : ℝ)| ≤ η / (K * Q')

/-- The `j`-th short interval meets the bad intervals. -/
def MeetsBad (f : ℝ → ℝ) (M N η Q' K : ℝ) (j : ℕ) : Prop :=
  ∃ x ∈ shortInterval M N j, IsBadPoint f η Q' K x

open Classical in
/-- The number of short intervals with label `Q ≤ q ≤ 2Q` which meet the bad
intervals. -/
noncomputable def badFareyArcCount (f : ℝ → ℝ) (M N R Q η Q' K : ℝ) : ℕ :=
  ((shortIndices M N).filter fun j =>
    (∃ (a : ℤ) (q : ℕ), Q ≤ q ∧ (q : ℝ) ≤ 2 * Q ∧ IsFareyLabel f M N R j a q) ∧
      MeetsBad f M N η Q' K j).card

/-- **Lemma 2.4** (bad Farey arcs).  Under the hypotheses of Lemma 2.3,
with `η < 1`, `1 + M²/T ≤ Q' < η R` (2.10) and `Q' ≤ K` (see the module
docstring), for `Q ≥ R/2` the number of short intervals with label
`Q ≤ q ≤ 2Q` meeting the bad intervals is `O(η M R²/(N Q²) + M Q'/(N Q))`. -/
def huxley_lemma24 : Prop :=
  ∀ C₁ C₂ C₃ : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 1 ≤ C₃ →
    ∃ C : ℝ, ∀ (F : ℝ → ℝ) (T M H N Q η Q' K : ℝ) (R : ℕ), DerivConditions C₁ C₂ C₃ F →
      1 ≤ T → ArcParameters C₂ (phase F T M) M T H N R →
      0 < η → η < 1 → 1 + M ^ 2 / T ≤ Q' → Q' < η * R → Q' ≤ K → (R : ℝ) / 2 ≤ Q →
      (badFareyArcCount (phase F T M) M N R Q η Q' K : ℝ) ≤
        C * (η * M * (R : ℝ) ^ 2 / (N * Q ^ 2) + M * Q' / (N * Q))

/-- `a/q` lies in a reference interval `e/r ≤ a/q ≤ f/s` of adjacent
fractions (`fr - es = 1`) satisfying (2.13):
`min(r, s) ≤ Q'` and `A ≤ max(r, s)/min(r, s) ≤ 2A`. -/
def InReferenceInterval (a : ℤ) (q : ℕ) (Q' A : ℝ) : Prop :=
  ∃ (e f : ℤ) (r s : ℕ), 1 ≤ r ∧ 1 ≤ s ∧ f * (r : ℤ) - e * (s : ℤ) = 1 ∧
    (e : ℝ) / (r : ℝ) ≤ (a : ℝ) / (q : ℝ) ∧ (a : ℝ) / (q : ℝ) ≤ (f : ℝ) / (s : ℝ) ∧
    min (r : ℝ) (s : ℝ) ≤ Q' ∧
    A ≤ max (r : ℝ) (s : ℝ) / min (r : ℝ) (s : ℝ) ∧
    max (r : ℝ) (s : ℝ) / min (r : ℝ) (s : ℝ) ≤ 2 * A

open Classical in
/-- `W_A`: the number of short intervals whose label lies in a reference
interval satisfying (2.13). -/
noncomputable def referenceArcCount (f : ℝ → ℝ) (M N R Q' A : ℝ) : ℕ :=
  ((shortIndices M N).filter fun j =>
    ∃ (a : ℤ) (q : ℕ), IsFareyLabel f M N R j a q ∧ InReferenceInterval a q Q' A).card

open Classical in
/-- `W_A(Q)`: the number of short intervals with label `Q ≤ q ≤ 2Q` lying in a
reference interval satisfying (2.13) and outside the bad intervals. -/
noncomputable def goodReferenceArcCount (f : ℝ → ℝ) (M N R Q Q' A η K : ℝ) : ℕ :=
  ((shortIndices M N).filter fun j =>
    (∃ (a : ℤ) (q : ℕ), Q ≤ q ∧ (q : ℝ) ≤ 2 * Q ∧ IsFareyLabel f M N R j a q ∧
        InReferenceInterval a q Q' A) ∧
      ¬ MeetsBad f M N η Q' K j).card

/-- **Lemma 2.5** (large partial quotients).  Under the hypotheses of
Lemma 2.4 and `A ≥ 1`: (2.14) `W_A = O(M log N/(A N))`, and (2.15) for
`Q ≥ R/2`, `W_A(Q) = O(M R² log N/(A N Q²))`. -/
def huxley_lemma25 : Prop :=
  ∀ C₁ C₂ C₃ : ℝ, 1 ≤ C₁ → 1 ≤ C₂ → 1 ≤ C₃ →
    ∃ C : ℝ, ∀ (F : ℝ → ℝ) (T M H N Q η Q' K A : ℝ) (R : ℕ), DerivConditions C₁ C₂ C₃ F →
      1 ≤ T → ArcParameters C₂ (phase F T M) M T H N R →
      0 < η → η < 1 → 1 + M ^ 2 / T ≤ Q' → Q' < η * R → Q' ≤ K → 1 ≤ A →
      (referenceArcCount (phase F T M) M N R Q' A : ℝ) ≤ C * (M * Real.log N / (A * N)) ∧
        ((R : ℝ) / 2 ≤ Q →
          (goodReferenceArcCount (phase F T M) M N R Q Q' A η K : ℝ) ≤
            C * (M * (R : ℝ) ^ 2 * Real.log N / (A * N * Q ^ 2)))

end LeanProofs.IntegerPoints
