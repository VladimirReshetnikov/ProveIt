import IntegerPoints.ExponentialSums
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Basic

/-!
# Fouvry–Iwaniec, *Exponential sums with monomials*

Formal statements (no proofs) of every numbered result of

> É. Fouvry and H. Iwaniec, Exponential sums with monomials,
> J. Number Theory 33 (1989), 311–333,

transcribed in `Papers/Exponential sums with monomials.tex`: Proposition 1 (the
double large sieve (1.6)), Corollary 1, Theorems 1–7, Proposition 2, Lemmas
2–9, and the final Corollary of §7.  Lemma 1 of the paper is Zhai–Cao's
Lemma 6, already stated as `zhaiCao_lemma6` (and proved in
`IntegerPoints.FouvryIwaniec`); its counting function `quadrupleCount` is
reused here.

Every statement is a `Prop`-valued definition; nothing is asserted.

## Conventions

* `≪` with an implied constant depending on parameters `p` is rendered as
  `∀ p, ∃ C, ∀ (everything else), ‖A‖ ≤ C * B`; hypotheses `f ≍ F` are
  rendered with explicit constants `c₁, c₂` quantified before `C`.
* The dyadic block `m ∼ M` of a *sum* is `dyadic M = (M, 2M]` (the paper
  writes `M ≤ m < 2M`); the dyadic block of a *counting function* is the
  closed range `closedRange M (2M) = [M, 2M]`, matching `quadrupleCount`.
  Sums over `M < m < μM` (Lemmas 5–7) use `openRange`, sums over
  `H' ≤ h < H` use `halfOpenRange`.
* Coefficient sequences are `ℕ → ℂ` (or `ℕ → ℕ → ℂ`) with `UnitBounded` /
  `UnitBounded₂`; the sieve coefficients of §7 are *real* (the factor `2` in
  Lemma 9 depends on this), with `UnitBoundedR`.  The Weyl-shift Lemma 2
  concerns an arbitrary real interval `[K, L)` and so takes `z : ℤ → ℂ`.
* The "`A`-spaced sequences" of Proposition 1 and Corollary 1 are functions
  `Fin R → ℝ`.
* Integrands with a removable singularity at `t = 0` (Lemmas 6 and 7) are
  written with Lean's `t⁻¹`, which vanishes at `t = 0`; this changes the
  integrand at a single point only.
* Where the paper leaves a hypothesis implicit (`M, Q ≥ 1` in the counting
  results of §4, `M, N ≥ 1` in §7) it is made explicit.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

/-! ### Helper notions -/

/-- The integers `n` with `A < n < B`, as a finset of naturals (for `A ≥ 0`). -/
noncomputable def openRange (A B : ℝ) : Finset ℕ := Finset.Ioo ⌊A⌋₊ ⌈B⌉₊

/-- The integers `n` with `A ≤ n < B`, as a finset of naturals (for `A ≥ 0`). -/
noncomputable def halfOpenRange (A B : ℝ) : Finset ℕ := Finset.Ico ⌈A⌉₊ ⌈B⌉₊

/-- The `ℓ²`-norm `‖φ‖ = (∑_r |φ_r|²)^{1/2}` of a finite sequence. -/
noncomputable def l2Norm {ι : Type*} [Fintype ι] (φ : ι → ℂ) : ℝ :=
  Real.sqrt (∑ r, ‖φ r‖ ^ 2)

/-- The `ℓ²`-norm of `φ` restricted to the index set `s`. -/
noncomputable def l2NormOn (s : Finset ℕ) (φ : ℕ → ℂ) : ℝ :=
  Real.sqrt (∑ m ∈ s, ‖φ m‖ ^ 2)

/-- A bounded real sequence of coefficients, `|a n| ≤ 1`. -/
def UnitBoundedR (a : ℕ → ℝ) : Prop := ∀ n, |a n| ≤ 1

/-! ### §1–2: the double large sieve and its direct consequences -/

/-- The bilinear form `𝓑_{φψ}(𝒳, 𝒴) = ∑_r ∑_s φ_r ψ_s e(x_r y_s)` of (1.4). -/
noncomputable def bilinearForm {R S : ℕ} (x : Fin R → ℝ) (y : Fin S → ℝ)
    (φ : Fin R → ℂ) (ψ : Fin S → ℂ) : ℂ :=
  ∑ r, ∑ s, φ r * ψ s * e (x r * y s)

open Classical in
/-- The spacing sum `𝓑_φ(𝒳, Y) = ∑_{|x_{r₁} - x_{r₂}| ≤ Y⁻¹} |φ_{r₁} φ_{r₂}|`
of Proposition 1. -/
noncomputable def spacingSum {R : ℕ} (x : Fin R → ℝ) (φ : Fin R → ℂ) (Y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin R × Fin R)).filter
      (fun p : Fin R × Fin R => |x p.1 - x p.2| ≤ Y⁻¹),
    ‖φ p.1‖ * ‖φ p.2‖

/-- **Fouvry–Iwaniec, Proposition 1** (the double large sieve (1.6),
Bombieri–Iwaniec).  For finite real sequences with `|x_r| ≤ X`, `|y_s| ≤ Y`,
`|𝓑_{φψ}(𝒳, 𝒴)|² ≤ 20 (1 + XY) 𝓑_φ(𝒳, Y) 𝓑_ψ(𝒴, X)`. -/
def fouvryIwaniec_prop1 : Prop :=
  ∀ (R S : ℕ) (X Y : ℝ) (x : Fin R → ℝ) (y : Fin S → ℝ) (φ : Fin R → ℂ) (ψ : Fin S → ℂ),
    0 < X → 0 < Y → (∀ r, |x r| ≤ X) → (∀ s, |y s| ≤ Y) →
    ‖bilinearForm x y φ ψ‖ ^ 2 ≤ 20 * (1 + X * Y) * spacingSum x φ Y * spacingSum y ψ X

/-- A finite real sequence is `A`-spaced: `|x_{r₁} - x_{r₂}| ≥ A` for `r₁ ≠ r₂`. -/
def IsSpaced {R : ℕ} (x : Fin R → ℝ) (A : ℝ) : Prop :=
  ∀ r₁ r₂ : Fin R, r₁ ≠ r₂ → A ≤ |x r₁ - x r₂|

/-- **Fouvry–Iwaniec, Corollary 1.**  If `𝒳` is `A`-spaced and `𝒴` is
`B`-spaced (with `|x_r| ≤ X`, `|y_s| ≤ Y`), then
`|𝓑_{φψ}(𝒳, 𝒴)| ≤ 5 (1 + XY)^{1/2} (1 + 1/(AY))^{1/2} (1 + 1/(BX))^{1/2} ‖φ‖ ‖ψ‖`. -/
def fouvryIwaniec_corollary1 : Prop :=
  ∀ (R S : ℕ) (X Y A B : ℝ) (x : Fin R → ℝ) (y : Fin S → ℝ) (φ : Fin R → ℂ) (ψ : Fin S → ℂ),
    0 < X → 0 < Y → 0 < A → 0 < B → (∀ r, |x r| ≤ X) → (∀ s, |y s| ≤ Y) →
    IsSpaced x A → IsSpaced y B →
    ‖bilinearForm x y φ ψ‖ ≤
      5 * (1 + X * Y) ^ ((1 : ℝ) / 2) * (1 + 1 / (A * Y)) ^ ((1 : ℝ) / 2) *
        (1 + 1 / (B * X)) ^ ((1 : ℝ) / 2) * l2Norm φ * l2Norm ψ

/-- The bilinear sum `S_{φψ}(M, N) = ∑_{m ∼ M} ∑_{n ∼ N} φ_m ψ_n e(f(m) g(n))`
of Theorem 1. -/
noncomputable def smoothBilinearSum (f g : ℝ → ℝ) (M N : ℝ) (φ ψ : ℕ → ℂ) : ℂ :=
  ∑ m ∈ dyadic M, ∑ n ∈ dyadic N, φ m * ψ n * e (f m * g n)

/-- **Fouvry–Iwaniec, Theorem 1.**  If `f ≍ F`, `f' ≍ F/M` on `[M, 2M]` and
`g ≍ G`, `g' ≍ G/N` on `[N, 2N]` (with `F, G, M, N > 0`), then
`S_{φψ}(M, N) ≪ (FG)^{-1/2} (FG + M)^{1/2} (FG + N)^{1/2} ‖φ‖ ‖ψ‖`.
The relations `≍` are rendered with common constants `c₁ ≤ · ≤ c₂` (any
family of constants can be reduced to this form), and "smooth" is read as
`C¹`, which is all the mean-value argument uses. -/
def fouvryIwaniec_theorem1 : Prop :=
  ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
    ∃ C : ℝ, ∀ (F G M N : ℝ) (f g : ℝ → ℝ) (φ ψ : ℕ → ℂ),
      0 < F → 0 < G → 0 < M → 0 < N → ContDiff ℝ 1 f → ContDiff ℝ 1 g →
      (∀ t ∈ Set.Icc M (2 * M), c₁ * F ≤ |f t| ∧ |f t| ≤ c₂ * F) →
      (∀ t ∈ Set.Icc M (2 * M), c₁ * F / M ≤ |deriv f t| ∧ |deriv f t| ≤ c₂ * F / M) →
      (∀ t ∈ Set.Icc N (2 * N), c₁ * G ≤ |g t| ∧ |g t| ≤ c₂ * G) →
      (∀ t ∈ Set.Icc N (2 * N), c₁ * G / N ≤ |deriv g t| ∧ |deriv g t| ≤ c₂ * G / N) →
      ‖smoothBilinearSum f g M N φ ψ‖ ≤
        C * ((F * G) ^ (-(1 : ℝ) / 2) * (F * G + M) ^ ((1 : ℝ) / 2) *
          (F * G + N) ^ ((1 : ℝ) / 2) * l2NormOn (dyadic M) φ * l2NormOn (dyadic N) ψ)

/-- The quadrinomial sum
`S_{φψ}(M₁, M₂, M₃, M₄) = ∑_{m_j ∼ M_j} φ_{m₁m₂} ψ_{m₃m₄}
   e(x m₁^{α₁} m₂^{α₂} m₃^{α₃} m₄^{α₄} / (M₁^{α₁} M₂^{α₂} M₃^{α₃} M₄^{α₄}))`
of Theorem 2. -/
noncomputable def quadSum (α₁ α₂ α₃ α₄ x M₁ M₂ M₃ M₄ : ℝ) (φ ψ : ℕ → ℕ → ℂ) : ℂ :=
  ∑ m₁ ∈ dyadic M₁, ∑ m₂ ∈ dyadic M₂, ∑ m₃ ∈ dyadic M₃, ∑ m₄ ∈ dyadic M₄,
    φ m₁ m₂ * ψ m₃ m₄ *
      e (x * ((m₁ : ℝ) ^ α₁ * (m₂ : ℝ) ^ α₂ * (m₃ : ℝ) ^ α₃ * (m₄ : ℝ) ^ α₄) /
        (M₁ ^ α₁ * M₂ ^ α₂ * M₃ ^ α₃ * M₄ ^ α₄))

/-- **Fouvry–Iwaniec, Theorem 2.**  For `α_j ≠ 0`, `M_j ≥ 1`, `x > 0` and
`|φ_{m₁m₂}|, |ψ_{m₃m₄}| ≤ 1`,
`S_{φψ}(M₁, M₂, M₃, M₄) ≪ {(x M₁M₂M₃M₄)^{1/2} + M₁M₂(M₃M₄)^{1/2}
   + (M₁M₂)^{1/2} M₃M₄ + x^{-1/2} M₁M₂M₃M₄} log(2 M₁M₂M₃M₄)`. -/
def fouvryIwaniec_theorem2 : Prop :=
  ∀ α₁ α₂ α₃ α₄ : ℝ, α₁ ≠ 0 → α₂ ≠ 0 → α₃ ≠ 0 → α₄ ≠ 0 →
    ∃ C : ℝ, ∀ (x M₁ M₂ M₃ M₄ : ℝ) (φ ψ : ℕ → ℕ → ℂ),
      0 < x → 1 ≤ M₁ → 1 ≤ M₂ → 1 ≤ M₃ → 1 ≤ M₄ → UnitBounded₂ φ → UnitBounded₂ ψ →
      ‖quadSum α₁ α₂ α₃ α₄ x M₁ M₂ M₃ M₄ φ ψ‖ ≤
        C * (((x * M₁ * M₂ * M₃ * M₄) ^ ((1 : ℝ) / 2) +
              M₁ * M₂ * (M₃ * M₄) ^ ((1 : ℝ) / 2) +
              (M₁ * M₂) ^ ((1 : ℝ) / 2) * M₃ * M₄ +
              x ^ (-(1 : ℝ) / 2) * M₁ * M₂ * M₃ * M₄) *
          Real.log (2 * M₁ * M₂ * M₃ * M₄))

/-! ### §3: two combinations with the Weyl shift -/

/-- **Fouvry–Iwaniec, Lemma 2** (the Weyl shift).  For `L > K`, `Q > 0` and
complex `z_k` (`k ∈ ℤ`),
`|∑_{K ≤ k < L} z_k|² ≤ (2 + (L - K)/Q) ∑_{|q| < Q} (1 - |q|/Q)
   ∑_{K ≤ k - |q|, k + |q| < L} z_{k-q} \overline{z_{k+q}}`
(the right-hand side is real; we take its real part).  The paper prints the
inner condition as `K ≤ k - q, k + q < L`, which for `q < 0` would let
`z_{k-q}` leave the interval; the symmetric condition in `|q|` is the
intended one. -/
def fouvryIwaniec_lemma2 : Prop :=
  ∀ (K L Q : ℝ) (z : ℤ → ℂ), K < L → 0 < Q →
    ‖∑ k ∈ Finset.Ico ⌈K⌉ ⌈L⌉, z k‖ ^ 2 ≤
      (2 + (L - K) / Q) *
        (∑ q ∈ Finset.Ioo (-⌈Q⌉) ⌈Q⌉, ((1 - |(q : ℝ)| / Q : ℝ) : ℂ) *
          ∑ k ∈ Finset.Ico (⌈K⌉ + |q|) (⌈L⌉ - |q|),
            z (k - q) * starRingEnd ℂ (z (k + q))).re

/-- **Fouvry–Iwaniec, Theorem 3.**  For `α ≠ 1`, `α α₁ α₂ ≠ 0`,
`M, M₁, M₂, x ≥ 1`, `|φ_m| ≤ 1`, `|ψ_{m₁m₂}| ≤ 1`, the sum
`S_{φψ}(M, M₁, M₂) = ∑_{m ∼ M} ∑_{m₁ ∼ M₁} ∑_{m₂ ∼ M₂} φ_m ψ_{m₁m₂}
   e(x m^α m₁^{α₁} m₂^{α₂} / (M^α M₁^{α₁} M₂^{α₂}))`
(which is `tripleSumII α α₁ α₂ x M M₁ M₂ φ ψ`) satisfies
`S_{φψ} ≪ {x^{1/4} M^{1/2} (M₁M₂)^{3/4} + M^{7/10} M₁M₂ + M (M₁M₂)^{3/4}
   + x^{-1/4} M^{11/10} M₁M₂} (log(2 M M₁M₂))²`. -/
def fouvryIwaniec_theorem3 : Prop :=
  ∀ α α₁ α₂ : ℝ, α ≠ 1 → α * α₁ * α₂ ≠ 0 →
    ∃ C : ℝ, ∀ (x M M₁ M₂ : ℝ) (φ : ℕ → ℂ) (ψ : ℕ → ℕ → ℂ),
      1 ≤ x → 1 ≤ M → 1 ≤ M₁ → 1 ≤ M₂ → UnitBounded φ → UnitBounded₂ ψ →
      ‖tripleSumII α α₁ α₂ x M M₁ M₂ φ ψ‖ ≤
        C * ((x ^ ((1 : ℝ) / 4) * M ^ ((1 : ℝ) / 2) * (M₁ * M₂) ^ ((3 : ℝ) / 4) +
              M ^ ((7 : ℝ) / 10) * M₁ * M₂ +
              M * (M₁ * M₂) ^ ((3 : ℝ) / 4) +
              x ^ (-(1 : ℝ) / 4) * M ^ ((11 : ℝ) / 10) * M₁ * M₂) *
          Real.log (2 * M * M₁ * M₂) ^ 2)

/-- **Fouvry–Iwaniec, Theorem 4.**  For `α₁, α₂ ∉ {0, 1}`, `M₁, M₂, x ≥ 1`
and `|φ_{m₁}|, |ψ_{m₂}| ≤ 1`, the bilinear sum
`S_{φψ}(M₁, M₂) = ∑_{m₁ ∼ M₁} ∑_{m₂ ∼ M₂} φ_{m₁} ψ_{m₂}
   e(x m₁^{α₁} m₂^{α₂} / (M₁^{α₁} M₂^{α₂}))`
(which is `doubleSumII α₁ α₂ x M₁ M₂ φ ψ`) satisfies
`S_{φψ} ≪ {x^{1/8} (M₁M₂)^{3/4} + M₁^{4/5} M₂ + M₁ M₂^{17/20}
   + x^{-1/8} (M₁M₂)^{21/20}} (log(2 M₁M₂))²`. -/
def fouvryIwaniec_theorem4 : Prop :=
  ∀ α₁ α₂ : ℝ, α₁ ≠ 0 → α₁ ≠ 1 → α₂ ≠ 0 → α₂ ≠ 1 →
    ∃ C : ℝ, ∀ (x M₁ M₂ : ℝ) (φ ψ : ℕ → ℂ),
      1 ≤ x → 1 ≤ M₁ → 1 ≤ M₂ → UnitBounded φ → UnitBounded ψ →
      ‖doubleSumII α₁ α₂ x M₁ M₂ φ ψ‖ ≤
        C * ((x ^ ((1 : ℝ) / 8) * (M₁ * M₂) ^ ((3 : ℝ) / 4) +
              M₁ ^ ((4 : ℝ) / 5) * M₂ +
              M₁ * M₂ ^ ((17 : ℝ) / 20) +
              x ^ (-(1 : ℝ) / 8) * (M₁ * M₂) ^ ((21 : ℝ) / 20)) *
          Real.log (2 * M₁ * M₂) ^ 2)

/-! ### §4: the spacing problem -/

/-- The Weyl-shifted point `t(m, q) = (m + q)^α - (m - q)^α`. -/
noncomputable def weylShiftPoint (α : ℝ) (m q : ℕ) : ℝ :=
  ((m : ℝ) + q) ^ α - ((m : ℝ) - q) ^ α

open Classical in
/-- The number `𝓑(M, Q, Δ)` of quadruples `(m, m̃, q, q̃)` with
`M ≤ m, m̃ ≤ 2M`, `Q ≤ q, q̃ ≤ 2Q` and `|t(m, q) - t(m̃, q̃)| < Δ T`, where
`T = M^{α-1} Q` (§4, (4.1)). -/
noncomputable def shiftQuadrupleCount (α M Q Δ : ℝ) : ℕ :=
  ((closedRange M (2 * M) ×ˢ closedRange M (2 * M) ×ˢ
      closedRange Q (2 * Q) ×ˢ closedRange Q (2 * Q)).filter
    fun p : ℕ × ℕ × ℕ × ℕ =>
      |weylShiftPoint α p.1 p.2.2.1 - weylShiftPoint α p.2.1 p.2.2.2| <
        Δ * (M ^ (α - 1) * Q)).card

/-- **Fouvry–Iwaniec, Proposition 2.**  For `α ≠ 0, 1`, `3Q < M` and
`Q ≤ M^{2/3}`,
`𝓑(M, Q, Δ) ≪ (MQ + Δ M² Q² + M^{-2} Q⁶) (log(2M))⁴`,
the implied constant depending on `α` only. -/
def fouvryIwaniec_prop2 : Prop :=
  ∀ α : ℝ, α ≠ 0 → α ≠ 1 →
    ∃ C : ℝ, ∀ M Q Δ : ℝ, 1 ≤ M → 1 ≤ Q → 0 < Δ → 3 * Q < M → Q ≤ M ^ ((2 : ℝ) / 3) →
      (shiftQuadrupleCount α M Q Δ : ℝ) ≤
        C * ((M * Q + Δ * M ^ 2 * Q ^ 2 + M ^ (-(2 : ℝ)) * Q ^ 6) * Real.log (2 * M) ^ 4)

open Classical in
/-- The number `𝓒(A, B, M, Δ)` of integers `M ≤ m ≤ 2M` with
`‖A m - B m⁻¹‖ < Δ` (Lemma 3). -/
noncomputable def lemma3Count (A B M Δ : ℝ) : ℕ :=
  ((closedRange M (2 * M)).filter
    fun m : ℕ => nearestIntDist (A * m - B / m) < Δ).card

open Classical in
/-- **Fouvry–Iwaniec, Lemma 3.**  If `0 < B < Δ M²`, then
`𝓒(A, B, M, Δ) ≪ Δ M ∑_{0 ≤ s < Δ⁻¹} (1 + ‖sA‖ M)⁻¹
   + Δ B^{-1/2} M^{3/2} ∑_{0 < s < Δ⁻¹, ‖sA‖ < 2 s B M⁻²} s^{-1/2}`,
with an absolute implied constant. -/
def fouvryIwaniec_lemma3 : Prop :=
  ∃ C : ℝ, ∀ A B M Δ : ℝ, 1 ≤ M → 0 < Δ → 0 < B → B < Δ * M ^ 2 →
    (lemma3Count A B M Δ : ℝ) ≤
      C * (Δ * M * ∑ s ∈ Finset.range ⌈Δ⁻¹⌉₊, (1 + nearestIntDist (s * A) * M)⁻¹ +
        Δ * B ^ (-(1 : ℝ) / 2) * M ^ ((3 : ℝ) / 2) *
          ∑ s ∈ (Finset.Ico 1 ⌈Δ⁻¹⌉₊).filter
              (fun s : ℕ => nearestIntDist (s * A) < 2 * s * B / M ^ 2),
            (s : ℝ) ^ (-(1 : ℝ) / 2))

open Classical in
/-- The number `𝓓(M, Q, Δ)` of triples `(m, q, q̃)` with `M ≤ m ≤ 2M`,
`Q ≤ q, q̃ ≤ 2Q` and `‖(q/q̃)^γ m - B(q, q̃) m⁻¹‖ < Δ` (Lemma 4). -/
noncomputable def lemma4Count (γ M Q Δ : ℝ) (B : ℕ → ℕ → ℝ) : ℕ :=
  ((closedRange M (2 * M) ×ˢ closedRange Q (2 * Q) ×ˢ closedRange Q (2 * Q)).filter
    fun p : ℕ × ℕ × ℕ =>
      nearestIntDist (((p.2.1 : ℝ) / p.2.2) ^ γ * p.1 - B p.2.1 p.2.2 / p.1) < Δ).card

/-- **Fouvry–Iwaniec, Lemma 4.**  Let `A(q/q̃) = (q/q̃)^γ` with `γ ≠ 0` and
`|B(q, q̃)| ≍ |q - q̃| Q` for `Q ≤ q, q̃ ≤ 2Q`.  If `Q < M^{2/3}`, then
`𝓓(M, Q, Δ) ≪ (MQ + Δ M Q² + Q^{8/3}) (log(2M))⁴`
(the implied constant depending on `γ` and the constants in `≍`). -/
def fouvryIwaniec_lemma4 : Prop :=
  ∀ γ c₁ c₂ : ℝ, γ ≠ 0 → 0 < c₁ → 0 < c₂ →
    ∃ C : ℝ, ∀ (M Q Δ : ℝ) (B : ℕ → ℕ → ℝ), 1 ≤ M → 1 ≤ Q → 0 < Δ → Q < M ^ ((2 : ℝ) / 3) →
      (∀ q ∈ closedRange Q (2 * Q), ∀ q' ∈ closedRange Q (2 * Q),
        c₁ * |(q : ℝ) - q'| * Q ≤ |B q q'| ∧ |B q q'| ≤ c₂ * |(q : ℝ) - q'| * Q) →
      (lemma4Count γ M Q Δ B : ℝ) ≤
        C * ((M * Q + Δ * M * Q ^ 2 + Q ^ ((8 : ℝ) / 3)) * Real.log (2 * M) ^ 4)

/-! ### §5: the Weyl shift combined with Poisson summation -/

/-- The weighted monomial sum `∑_{M < m < μM} m^{-1/2} e(α⁻¹ m^α M^{-α} X)`
of Lemmas 5 and 7. -/
noncomputable def monomialPhaseSum (α X M μ : ℝ) : ℂ :=
  ∑ m ∈ openRange M (μ * M),
    (((m : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * e (α⁻¹ * (m : ℝ) ^ α * M ^ (-α) * X)

/-- The range of the dual variable in Lemma 5: the integers strictly between
`N` and `νN` (in either order). -/
noncomputable def bProcessRange (N ν : ℝ) : Finset ℕ :=
  openRange (min N (ν * N)) (max N (ν * N))

/-- **Fouvry–Iwaniec, Lemma 5** (van der Corput's B-process for monomials).
For `X, M > 0`, `μ > 1`, `α ≠ 0, 1`, with `β = α/(α-1)`, `ν = μ^{α-1}`,
`N = X/M`,
`∑_{M < m < μM} m^{-1/2} e(α⁻¹ m^α M^{-α} X)
   = γ ∑_{N < n < νN} n^{-1/2} e(-β⁻¹ n^β N^{-β} X)
     + O(M^{-1/2} log(2 + M) + N^{-1/2} log(2 + N))`,
where `γ` depends on `α` alone, the implied constant on `α` and `μ`, and the
`n`-range is read as `νN < n < N` when `ν < 1`. -/
def fouvryIwaniec_lemma5 : Prop :=
  ∀ α : ℝ, α ≠ 0 → α ≠ 1 →
    ∃ γ : ℂ, ∀ μ : ℝ, 1 < μ →
      ∃ C : ℝ, ∀ X M : ℝ, 0 < X → 0 < M →
        ‖monomialPhaseSum α X M μ -
            γ * ∑ n ∈ bProcessRange (X / M) (μ ^ (α - 1)),
              (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
                e (-(α / (α - 1))⁻¹ * (n : ℝ) ^ (α / (α - 1)) *
                  (X / M) ^ (-(α / (α - 1))) * X)‖ ≤
          C * (M ^ (-(1 : ℝ) / 2) * Real.log (2 + M) +
                (X / M) ^ (-(1 : ℝ) / 2) * Real.log (2 + X / M))

/-- **Fouvry–Iwaniec, Lemma 6** (separation of variables by a Perron-type
integral).  For `0 < L ≤ N < νN < λL` and `|a_l| ≤ 1`,
`∑_{N < n < νN} a_n = (2πi)⁻¹ ∫_{-L}^{L} (∑_{L < l < λL} a_l l^{-it}) N^{it} (ν^{it} - 1) t⁻¹ dt
   + O(log(2 + L))`,
the implied constant depending on `λ` only.  (The paper prints `(2π)⁻¹`; the
Perron normalisation is `(2πi)⁻¹`, see the `% ed.:` note in the transcription.) -/
def fouvryIwaniec_lemma6 : Prop :=
  ∀ lam : ℝ, 1 < lam →
    ∃ C : ℝ, ∀ (L N ν : ℝ) (a : ℕ → ℂ), UnitBounded a →
      0 < L → L ≤ N → 1 < ν → ν * N < lam * L →
      ‖(∑ n ∈ openRange N (ν * N), a n) -
          (1 / (2 * Real.pi * Complex.I)) *
            ∫ t in (-L)..L,
              (∑ l ∈ openRange L (lam * L), a l / (l : ℂ) ^ (Complex.I * t)) *
                ((N : ℂ) ^ (Complex.I * t) * ((ν : ℂ) ^ (Complex.I * t) - 1) / (t : ℂ))‖ ≤
        C * Real.log (2 + L)

/-- The constant `λ = 2 (μ^{α-1} + μ^{1-α})` of Lemma 7. -/
noncomputable def poissonLambda (μ α : ℝ) : ℝ := 2 * (μ ^ (α - 1) + μ ^ (1 - α))

/-- **Fouvry–Iwaniec, Lemma 7** (Lemmas 5 and 6 combined).  For `X, M > 0`,
`μ > 1`, `α ≠ 0, 1`, `β = α/(α-1)`, `λ = 2(μ^{α-1} + μ^{1-α})` and any `L`
with `1/2 < LM/X < 2`,
`∑_{M < m < μM} m^{-1/2} e(α⁻¹ m^α M^{-α} X)
   = (γ/2πi) ∫_{-L}^{L} (∑_{λ⁻¹L < l < λL} l^{-1/2} (X/(lM))^{it} e(-β⁻¹ (lM/X)^β X))
       (μ^{i(α-1)t} - 1) t⁻¹ dt
     + O(M^{-1/2} log(2 + M) + L^{-1/2} log(2 + L))`,
where `γ` depends on `α` alone and the implied constant on `α` and `μ`. -/
def fouvryIwaniec_lemma7 : Prop :=
  ∀ α : ℝ, α ≠ 0 → α ≠ 1 →
    ∃ γ : ℂ, ∀ μ : ℝ, 1 < μ →
      ∃ C : ℝ, ∀ X M L : ℝ, 0 < X → 0 < M → 1 / 2 < L * M / X → L * M / X < 2 →
        ‖monomialPhaseSum α X M μ -
            (γ / (2 * Real.pi * Complex.I)) *
              ∫ t in (-L)..L,
                (∑ l ∈ openRange ((poissonLambda μ α)⁻¹ * L) (poissonLambda μ α * L),
                  (((l : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
                    ((X / (l * M) : ℝ) : ℂ) ^ (Complex.I * t) *
                    e (-(α / (α - 1))⁻¹ * ((l : ℝ) * M / X) ^ (α / (α - 1)) * X)) *
                  (((μ : ℂ) ^ (Complex.I * ((α - 1) * t)) - 1) / (t : ℂ))‖ ≤
          C * (M ^ (-(1 : ℝ) / 2) * Real.log (2 + M) +
                L ^ (-(1 : ℝ) / 2) * Real.log (2 + L))

/-- The sum
`S_{φψ}(M₁, M₂, M₃, M₄) = ∑_{m_j ∼ M_j} φ_{m₁m₂} ψ_{m₃}
   e(x m₁^{α₁} m₂^{α₂} m₃^α m₄^{-α} / (M₁^{α₁} M₂^{α₂} M₃^α M₄^{-α}))`
of §5 (no coefficient on `m₄`). -/
noncomputable def quadSumPoisson (α α₁ α₂ x M₁ M₂ M₃ M₄ : ℝ) (φ : ℕ → ℕ → ℂ) (ψ : ℕ → ℂ) : ℂ :=
  ∑ m₁ ∈ dyadic M₁, ∑ m₂ ∈ dyadic M₂, ∑ m₃ ∈ dyadic M₃, ∑ m₄ ∈ dyadic M₄,
    φ m₁ m₂ * ψ m₃ *
      e (x * ((m₁ : ℝ) ^ α₁ * (m₂ : ℝ) ^ α₂ * (m₃ : ℝ) ^ α * (m₄ : ℝ) ^ (-α)) /
        (M₁ ^ α₁ * M₂ ^ α₂ * M₃ ^ α * M₄ ^ (-α)))

/-- **Fouvry–Iwaniec, Theorem 5.**  For `α ≠ -1`, `α α₁ α₂ ≠ 0`,
`M₁, M₂, M₃, M₄, x ≥ 1`, `|φ_{m₁m₂}| ≤ 1`, `|ψ_{m₃}| ≤ 1` and any `ε > 0`,
`S_{φψ}(M₁, M₂, M₃, M₄) ≪ {x^{1/2} (M₁M₂)^{3/4} M₃
   + x^{7/20} M₁M₂ M₃^{11/10} M₄^{-1/10} + x^{1/4} (M₁M₂)^{3/4} (M₃M₄)^{1/2}
   + x^{1/5} M₁M₂ M₃^{7/10} M₄^{3/10} + x^{-1/2} M₁M₂M₃M₄} (x M₁M₂M₃M₄)^ε`,
the implied constant depending on `α, α₁, α₂, ε` only. -/
def fouvryIwaniec_theorem5 : Prop :=
  ∀ α α₁ α₂ ε : ℝ, α ≠ -1 → α * α₁ * α₂ ≠ 0 → 0 < ε →
    ∃ C : ℝ, ∀ (x M₁ M₂ M₃ M₄ : ℝ) (φ : ℕ → ℕ → ℂ) (ψ : ℕ → ℂ),
      1 ≤ x → 1 ≤ M₁ → 1 ≤ M₂ → 1 ≤ M₃ → 1 ≤ M₄ → UnitBounded₂ φ → UnitBounded ψ →
      ‖quadSumPoisson α α₁ α₂ x M₁ M₂ M₃ M₄ φ ψ‖ ≤
        C * ((x ^ ((1 : ℝ) / 2) * (M₁ * M₂) ^ ((3 : ℝ) / 4) * M₃ +
              x ^ ((7 : ℝ) / 20) * M₁ * M₂ * M₃ ^ ((11 : ℝ) / 10) * M₄ ^ (-(1 : ℝ) / 10) +
              x ^ ((1 : ℝ) / 4) * (M₁ * M₂) ^ ((3 : ℝ) / 4) * (M₃ * M₄) ^ ((1 : ℝ) / 2) +
              x ^ ((1 : ℝ) / 5) * M₁ * M₂ * M₃ ^ ((7 : ℝ) / 10) * M₄ ^ ((3 : ℝ) / 10) +
              x ^ (-(1 : ℝ) / 2) * M₁ * M₂ * M₃ * M₄) *
          (x * M₁ * M₂ * M₃ * M₄) ^ ε)

/-! ### §6: a special sum -/

/-- The sum
`S_{χφψ}(H, M, N) = ∑_{h ∼ H} ∑_{m ∼ M} ∑_{n ∼ N} χ(h) φ_m ψ_n
   e(x h n⁻¹ m^α / (H N⁻¹ M^α))`
of §6, with the additive character `χ(h) = e(ξ h)`. -/
noncomputable def specialSum (α x ξ H M N : ℝ) (φ ψ : ℕ → ℂ) : ℂ :=
  ∑ h ∈ dyadic H, ∑ m ∈ dyadic M, ∑ n ∈ dyadic N,
    e (ξ * h) * φ m * ψ n *
      e (x * ((h : ℝ) * (n : ℝ)⁻¹ * (m : ℝ) ^ α) / (H * N⁻¹ * M ^ α))

/-- **Fouvry–Iwaniec, Theorem 6.**  For `α ≠ 0, 1`, `H, M, N, x ≥ 1`, an
additive character `χ(h) = e(ξh)` and `|φ_m|, |ψ_n| ≤ 1`,
`S_{χφψ}(H, M, N) ≪ (HMN)^{1/2} [(H + N)^{1/2} (x^{1/8} H^{-1/6} M^{1/12} N^{1/6}
   + x^{1/8} H^{-1/8} N^{3/8} + N^{1/2} + N^{1/4} M^{1/8}) x^{1/8}
   + M^{1/2} + x^{-1/4} M^{1/2} N] 𝓛⁴`,
`𝓛 = log(2HMNx)`, the implied constant depending on `α` only. -/
def fouvryIwaniec_theorem6 : Prop :=
  ∀ α : ℝ, α ≠ 0 → α ≠ 1 →
    ∃ C : ℝ, ∀ (x ξ H M N : ℝ) (φ ψ : ℕ → ℂ),
      1 ≤ x → 1 ≤ H → 1 ≤ M → 1 ≤ N → UnitBounded φ → UnitBounded ψ →
      ‖specialSum α x ξ H M N φ ψ‖ ≤
        C * ((H * M * N) ^ ((1 : ℝ) / 2) *
          ((H + N) ^ ((1 : ℝ) / 2) *
              (x ^ ((1 : ℝ) / 8) * H ^ (-(1 : ℝ) / 6) * M ^ ((1 : ℝ) / 12) * N ^ ((1 : ℝ) / 6) +
                x ^ ((1 : ℝ) / 8) * H ^ (-(1 : ℝ) / 8) * N ^ ((3 : ℝ) / 8) +
                N ^ ((1 : ℝ) / 2) + N ^ ((1 : ℝ) / 4) * M ^ ((1 : ℝ) / 8)) *
              x ^ ((1 : ℝ) / 8) +
            M ^ ((1 : ℝ) / 2) + x ^ (-(1 : ℝ) / 4) * M ^ ((1 : ℝ) / 2) * N) *
          Real.log (2 * H * M * N * x) ^ 4)

open Classical in
/-- The arithmetic function
`ω(r) = ∑_{H₁' ≤ h₁ < H₁, H₂' ≤ h₂ < H₂, h₁n₁ - h₂n₂ = r} e(ξ₁h₁ + ξ₂h₂)`
of Lemma 8, (6.2). -/
noncomputable def omegaCoeff (H₁' H₁ H₂' H₂ ξ₁ ξ₂ : ℝ) (n₁ n₂ : ℕ) (r : ℤ) : ℂ :=
  ∑ p ∈ (halfOpenRange H₁' H₁ ×ˢ halfOpenRange H₂' H₂).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) * n₁ - (p.2 : ℤ) * n₂ = r),
    e (ξ₁ * p.1 + ξ₂ * p.2)

/-- **Fouvry–Iwaniec, Lemma 8.**  For `H₁ ≥ H₁' ≥ 1`, `H₂ ≥ H₂' ≥ 1`, real
`ξ₁, ξ₂` and coprime positive integers `n₁, n₂`, there is a (continuous)
`ω̂ : ℝ → ℂ` with `ω(r) = ∫₀¹ ω̂(θ) e(θr) dθ` for all `r` (6.2) and
`∫₀¹ |ω̂(θ)| dθ ≪ (1 + H₁H₂/(n₁n₂))^{1/2} (log(2H₁H₂))²` (6.3), the implied
constant being absolute. -/
def fouvryIwaniec_lemma8 : Prop :=
  ∃ C : ℝ, ∀ (H₁ H₁' H₂ H₂' ξ₁ ξ₂ : ℝ) (n₁ n₂ : ℕ),
    1 ≤ H₁' → H₁' ≤ H₁ → 1 ≤ H₂' → H₂' ≤ H₂ → 0 < n₁ → 0 < n₂ → Nat.Coprime n₁ n₂ →
    ∃ ωhat : ℝ → ℂ, Continuous ωhat ∧
      (∀ r : ℤ, omegaCoeff H₁' H₁ H₂' H₂ ξ₁ ξ₂ n₁ n₂ r =
        ∫ θ in (0 : ℝ)..1, ωhat θ * e (θ * r)) ∧
      ∫ θ in (0 : ℝ)..1, ‖ωhat θ‖ ≤
        C * ((1 + H₁ * H₂ / (n₁ * n₂)) ^ ((1 : ℝ) / 2) * Real.log (2 * H₁ * H₂) ^ 2)

/-! ### §7: exponential sums related to short intervals -/

/-- The sieve remainder term `r_d = [x/d] - [(x - y)/d] - y/d`. -/
noncomputable def sieveRemainder (x y : ℝ) (d : ℕ) : ℝ :=
  ((⌊x / (d : ℝ)⌋ : ℤ) : ℝ) - ((⌊(x - y) / (d : ℝ)⌋ : ℤ) : ℝ) - y / d

/-- The bilinear form `R(M, N) = ∑_{1 ≤ m < M} ∑_{1 ≤ n < N} a_m b_n r_{mn}` of
(7.1), with real coefficients. -/
noncomputable def sieveBilinear (x y M N : ℝ) (a b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ halfOpenRange 1 M, ∑ n ∈ halfOpenRange 1 N, a m * b n * sieveRemainder x y (m * n)

/-- The exponential sum
`S_z(H, M, N) = ∑_{1 ≤ h ≤ H} ∑_{1 ≤ m < M} ∑_{1 ≤ n < N} (a_m b_n / (mn)) e(hz/(mn))`
of §7. -/
noncomputable def sieveExpSum (z H M N : ℝ) (a b : ℕ → ℝ) : ℂ :=
  ∑ h ∈ upTo H, ∑ m ∈ halfOpenRange 1 M, ∑ n ∈ halfOpenRange 1 N,
    ((a m * b n / ((m : ℝ) * n) : ℝ) : ℂ) * e ((h : ℝ) * z / ((m : ℝ) * n))

/-- **Fouvry–Iwaniec, Lemma 9.**  For `1 ≤ y ≤ x/2`, `M, N ≥ 1` and real
`|a_m|, |b_n| ≤ 1`,
`|R(M, N)| ≤ 2 ∫_{x-2y}^{x+y} |S_z(H, M, N)| dz + O(y x^{-ε})`
with `H = MN y⁻¹ x^{3ε}`, the implied constant depending on `ε` alone. -/
def fouvryIwaniec_lemma9 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ (x y M N : ℝ) (a b : ℕ → ℝ),
      1 ≤ y → y ≤ x / 2 → 1 ≤ M → 1 ≤ N → UnitBoundedR a → UnitBoundedR b →
      |sieveBilinear x y M N a b| ≤
        2 * (∫ z in (x - 2 * y)..(x + y),
              ‖sieveExpSum z (M * N * y⁻¹ * x ^ (3 * ε)) M N a b‖) +
          C * (y * x ^ (-ε))

/-- The dyadic bilinear form `∑_{m ∼ M} ∑_{n ∼ N} a_m b_n r_{mn}` of (7.3). -/
noncomputable def sieveBilinearDyadic (x y M N : ℝ) (a b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ dyadic M, ∑ n ∈ dyadic N, a m * b n * sieveRemainder x y (m * n)

/-- **Fouvry–Iwaniec, Theorem 7.**  For `2 ≤ y ≤ x^{1/2}`, `M, N ≥ 1`, real
`|a_m|, |b_n| ≤ 1` and `ε' = 48ε`, if `M < y x^{-ε'}` (7.4),
`N⁶ < M y⁷ x^{-3-ε'}` (7.5) and `M² N⁴ < y x^{1-ε'}` (7.6), then
`∑_{m ∼ M} ∑_{n ∼ N} a_m b_n r_{mn} ≪ y x^{-ε}` (7.3), the implied constant
depending on `ε` alone. -/
def fouvryIwaniec_theorem7 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ (x y M N : ℝ) (a b : ℕ → ℝ),
      2 ≤ y → y ≤ x ^ ((1 : ℝ) / 2) → 1 ≤ M → 1 ≤ N → UnitBoundedR a → UnitBoundedR b →
      M < y * x ^ (-(48 * ε)) →
      N ^ 6 < M * y ^ 7 * x ^ (-3 - 48 * ε) →
      M ^ 2 * N ^ 4 < y * x ^ (1 - 48 * ε) →
      |sieveBilinearDyadic x y M N a b| ≤ C * (y * x ^ (-ε))

/-- **Fouvry–Iwaniec, Corollary (§7).**  For `x^{7/19} < y < x^{11/23}`
(and `y ≥ 2`), real `|a_m|, |b_n| ≤ 1` and `ε' = 48ε`, the bound
`R(M, N) ≪ y x^{-ε}` (7.2) holds provided `M < y x^{-ε'}` (7.4) and
`N < y^{19/16} x^{-7/16-ε'}` (7.11).  (The paper derives this from Theorem 7
together with the bound (7.10) of Halberstam–Heath-Brown–Richert and
Iwaniec–Laborde.) -/
def fouvryIwaniec_corollary7 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ (x y M N : ℝ) (a b : ℕ → ℝ),
      2 ≤ y → x ^ ((7 : ℝ) / 19) < y → y < x ^ ((11 : ℝ) / 23) → 1 ≤ M → 1 ≤ N →
      UnitBoundedR a → UnitBoundedR b →
      M < y * x ^ (-(48 * ε)) →
      N < y ^ ((19 : ℝ) / 16) * x ^ (-(7 : ℝ) / 16 - 48 * ε) →
      |sieveBilinear x y M N a b| ≤ C * (y * x ^ (-ε))

end LeanProofs.IntegerPoints
