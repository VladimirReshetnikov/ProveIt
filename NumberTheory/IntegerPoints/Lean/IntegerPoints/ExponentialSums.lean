import IntegerPoints.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exponential-sum lemmas quoted by the two papers

Formal statements (no proofs yet) of the auxiliary results in §2 of
Zhai–Cao and §2 of Wu.  Each statement is a `Prop`-valued definition named
after its source, so that this module carries no trust boundary: nothing here
is asserted, only *stated*.

## Conventions for `≪` and `∼`

* A bound `A ≪ B` whose implied constant is allowed to depend on parameters
  `p` is rendered as `∀ p, ∃ C, ∀ (everything else), ‖A‖ ≤ C * B`.
* Hypotheses of the form `|φ| ≪ Λ`, `|φ| ≫ Λ`, `|φ| ∼ Λ` are rendered with
  explicit constants `c₁, c₂, …` that are quantified *before* the implied
  constant `C`, so that `C` may depend on them (as in the papers).
* Functions of a real variable are taken globally `C^k` on `ℝ`
  (`ContDiff ℝ k f`) with hypotheses imposed only on the interval in
  question; `deriv` / `iteratedDeriv` are then the classical derivatives
  there.  Any `C^k` function on a closed interval extends to one on `ℝ`, so
  this loses no generality.
* Sums `∑_{N < n ≤ c N}` are over `intRange N (c * N)`, and `n ∼ N` is the
  dyadic block `dyadic N` (see `IntegerPoints.Basic`).
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

/-! ### Helper notions -/

/-- The edge term `min (1, L / (T ‖M‖))` of Perron's formula, read as `1`
when `M` is an integer (`‖M‖ = 0`). -/
noncomputable def perronEdge (L T M : ℝ) : ℝ :=
  if nearestIntDist M = 0 then 1 else min 1 (L / (T * nearestIntDist M))

/-- The Bombieri–Iwaniec kernel
`K(θ) = min (M₁ - M + 1, (π|θ|)⁻¹, (π|θ|)⁻²)`.  (At `θ = 0` Lean's `0⁻¹ = 0`
makes the value `0` instead of `M₁ - M + 1`; this is a single point and does
not affect the integrals below.) -/
noncomputable def biKernel (M M₁ θ : ℝ) : ℝ :=
  min (M₁ - M + 1) (min ((Real.pi * |θ|)⁻¹) ((Real.pi * |θ|)⁻¹ ^ 2))

/-- The integers `n` with `A ≤ n ≤ B`, as a finset of naturals. -/
noncomputable def closedRange (A B : ℝ) : Finset ℕ := Finset.Icc ⌈A⌉₊ ⌊B⌋₊

open Classical in
/-- The number `𝒜(M, N, Δ)` of quadruples `(m, m̃, n, ñ)` with
`M ≤ m, m̃ ≤ 2M`, `N ≤ n, ñ ≤ 2N` and `|(m̃/m)^α - (ñ/n)^β| < Δ`
(Zhai–Cao, Lemma 6). -/
noncomputable def quadrupleCount (α β M N Δ : ℝ) : ℕ :=
  ((closedRange M (2 * M) ×ˢ closedRange M (2 * M) ×ˢ
      closedRange N (2 * N) ×ˢ closedRange N (2 * N)).filter
    fun q : ℕ × ℕ × ℕ × ℕ =>
      |((q.2.1 : ℝ) / q.1) ^ α - ((q.2.2.2 : ℝ) / q.2.2.1) ^ β| < Δ).card

/-- `f` is an algebraic function on `s`: some nonzero real polynomial in two
variables vanishes on the graph of `f` over `s`. -/
def AlgebraicOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ P : MvPolynomial (Fin 2) ℝ, P ≠ 0 ∧ ∀ t ∈ s, MvPolynomial.eval ![t, f t] P = 0

open Classical in
/-- The weight `b_u` of the van der Corput B-process: `1` for `α < u < β`
and `1/2` at an integer endpoint. -/
noncomputable def bWeight (α β : ℝ) (u : ℤ) : ℝ :=
  if (u : ℝ) = α ∨ (u : ℝ) = β then 1 / 2 else 1

open Classical in
/-- `⟨t⟩` of Zhai–Cao, Lemma 7: `‖t‖` when `t` is not an integer, and
`β - α` otherwise. -/
noncomputable def angleBracket (α β t : ℝ) : ℝ :=
  if ∃ k : ℤ, (k : ℝ) = t then β - α else nearestIntDist t

/-- A bounded sequence of coefficients, `|a n| ≤ 1`. -/
def UnitBounded (a : ℕ → ℂ) : Prop := ∀ n, ‖a n‖ ≤ 1

/-- A bounded double sequence of coefficients, `|b m n| ≤ 1`. -/
def UnitBounded₂ (b : ℕ → ℕ → ℂ) : Prop := ∀ m n, ‖b m n‖ ≤ 1

/-! ### Zhai–Cao, §2, Lemmas 1–8 -/

/-- **Zhai–Cao, Lemma 1** (Kuz'min–Landau / van der Corput second-derivative
bound).  If `c₁ λ₁ ≤ |f'| ≤ c₂ λ₁` and `|f''| ∼ λ₁ / N` on `[N, c N]`, then
`∑_{N < n ≤ c N} e(f(n)) ≪ λ₁⁻¹ + λ₁^{1/2} N^{1/2}`. -/
def zhaiCao_lemma1 : Prop :=
  ∀ c c₁ c₂ c₃ c₄ : ℝ, 1 < c → 0 < c₁ → 0 < c₂ → 0 < c₃ → 0 < c₄ →
    ∃ C : ℝ, ∀ (N lam : ℝ) (f : ℝ → ℝ), 1 ≤ N → 0 < lam → ContDiff ℝ 2 f →
      (∀ t ∈ Set.Icc N (c * N), c₁ * lam ≤ |deriv f t| ∧ |deriv f t| ≤ c₂ * lam) →
      (∀ t ∈ Set.Icc N (c * N),
        c₃ * lam / N ≤ |iteratedDeriv 2 f t| ∧ |iteratedDeriv 2 f t| ≤ c₄ * lam / N) →
      ‖∑ n ∈ intRange N (c * N), e (f n)‖ ≤
        C * (lam⁻¹ + lam ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2))

/-- **Zhai–Cao, Lemma 2** (Perron's formula).  For `|a(n)| ≤ A`,
`1 ≤ L ≤ M < N ≤ c L` and `T ≥ 2`,
`∑_{M < n ≤ N} a(n) = (2πi)⁻¹ ∫_{-T}^{T} ∑_{L < l ≤ cL} a(l) l^{-it} (N^{it} - M^{it}) / t dt
  + O(min(1, L/(T‖M‖)) + min(1, L/(T‖N‖)) + L log(1 + L) / T)`. -/
def zhaiCao_lemma2 : Prop :=
  ∀ c A : ℝ, 1 < c → 0 < A →
    ∃ C : ℝ, ∀ (L M N T : ℝ) (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ A) →
      1 ≤ L → L ≤ M → M < N → N ≤ c * L → 2 ≤ T →
      ‖(∑ n ∈ intRange M N, a n) -
          (1 / (2 * Real.pi * Complex.I)) *
            ∫ t in (-T)..T,
              (∑ l ∈ intRange L (c * L), a l / (l : ℂ) ^ (Complex.I * t)) *
                (((N : ℂ) ^ (Complex.I * t) - (M : ℂ) ^ (Complex.I * t)) / t)‖ ≤
        C * (perronEdge L T M + perronEdge L T N + L * Real.log (1 + L) / T)

/-- **Zhai–Cao, Lemma 3** (Krätzel, Lemma 2.8).  If `|f| ≤ c₁ P` and
`|f'| ≥ c₂ Δ` on `[N, 2N]`, then
`∑_{n ∼ N} min(D, 1/‖f(n)‖) ≪ (P + 1)(D + Δ⁻¹) log(2 + Δ⁻¹)`. -/
def zhaiCao_lemma3 : Prop :=
  ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
    ∃ C : ℝ, ∀ (N P Δ D : ℝ) (f : ℝ → ℝ), 1 ≤ N → 0 < P → 0 < Δ → 0 < D →
      ContDiff ℝ 1 f →
      (∀ t ∈ Set.Icc N (2 * N), |f t| ≤ c₁ * P) →
      (∀ t ∈ Set.Icc N (2 * N), c₂ * Δ ≤ |deriv f t|) →
      ∑ n ∈ dyadic N, minInv D (nearestIntDist (f n)) ≤
        C * ((P + 1) * (D + Δ⁻¹) * Real.log (2 + Δ⁻¹))

/-- **Zhai–Cao, Lemma 4** (Weyl–van der Corput inequality).  For `1 ≤ Q ≤ N`,
`|∑_{N < n ≤ cN} a(n)|² ≪ (N/Q) ∑_{0 ≤ q ≤ Q} (1 - q/Q) ℜ ∑_{N < n ≤ cN - q} a(n) \overline{a(n+q)}`. -/
def zhaiCao_lemma4 : Prop :=
  ∀ c : ℝ, 1 < c →
    ∃ C : ℝ, ∀ (N Q : ℝ) (a : ℕ → ℂ), 1 ≤ Q → Q ≤ N →
      ‖∑ n ∈ intRange N (c * N), a n‖ ^ 2 ≤
        C * (N / Q) * ∑ q ∈ Finset.range (⌊Q⌋₊ + 1),
          (1 - q / Q) * (∑ n ∈ intRange N (c * N - q), a n * starRingEnd ℂ (a (n + q))).re

/-- **Zhai–Cao, Lemma 5** (Bombieri–Iwaniec, Lemma 2.2).  For
`M ≤ N < N₁ ≤ M₁`,
`|∑_{N < n ≤ N₁} a(n)| ≤ ∫ K(θ) |∑_{M < m ≤ M₁} a(m) e(mθ)| dθ`
with `K = biKernel M M₁`, and `∫ K(θ) dθ ≤ 3 log(2 + M₁ - M)`. -/
def zhaiCao_lemma5 : Prop :=
  (∀ (M N N₁ M₁ : ℝ) (a : ℕ → ℂ), 0 ≤ M → M ≤ N → N < N₁ → N₁ ≤ M₁ →
    ‖∑ n ∈ intRange N N₁, a n‖ ≤
      ∫ θ : ℝ, biKernel M M₁ θ * ‖∑ m ∈ intRange M M₁, a m * e (m * θ)‖) ∧
  (∀ M M₁ : ℝ, M ≤ M₁ → ∫ θ : ℝ, biKernel M M₁ θ ≤ 3 * Real.log (2 + M₁ - M))

/-- **Zhai–Cao, Lemma 6** (Fouvry–Iwaniec, Lemma 1).  For `αβ ≠ 0`,
`𝒜(M, N, Δ) ≪ M N log(2MN) + Δ M² N²`. -/
def zhaiCao_lemma6 : Prop :=
  ∀ α β : ℝ, α * β ≠ 0 →
    ∃ C : ℝ, ∀ M N Δ : ℝ, 1 ≤ M → 1 ≤ N → 0 < Δ →
      (quadrupleCount α β M N Δ : ℝ) ≤
        C * (M * N * Real.log (2 * M * N) + Δ * M ^ 2 * N ^ 2)

/-- **Zhai–Cao, Lemma 7** (Min, Theorem 2.2; the van der Corput
B-process with a smooth weight).  Let `f, g` be algebraic on `[a, b]` with
`f'' ∼ 1/R` (taken positive: for `f'' < 0` apply the statement to `-f` and
conjugate), `|f'''| ≪ 1/(RU)`, `|g| ≪ G`, `|g'| ≪ G/U₁`, `U, U₁ ≥ 1`.  Let
`[α, β] = f'([a, b])` and let `n_u ∈ [a, b]` solve `f'(n_u) = u`.  Then
`∑_{a < n ≤ b} g(n) e(f(n))
   = ∑_{α ≤ u ≤ β} b_u g(n_u) |f''(n_u)|^{-1/2} e(f(n_u) - u n_u + 1/8)
     + O(G log(β - α + 2) + G (b - a + R)(U⁻¹ + U₁⁻¹))
     + O(G min(√R, 1/⟨α⟩) + G min(√R, 1/⟨β⟩))`.
The sum over `u` is over all integers in `[α, β]` with `b_u = 1/2` at integer
endpoints, the standard form of the B-process (the printed paper writes
`α < u ≤ β` but defines `b_u` at `u = α` as well; the transcription has been
corrected to `α ≤ u ≤ β` with an `% ed.:` note). -/
def zhaiCao_lemma7 : Prop :=
  ∀ c₁ c₂ c₃ c₄ c₅ : ℝ, 0 < c₁ → 0 < c₂ → 0 < c₃ → 0 < c₄ → 0 < c₅ →
    ∃ C : ℝ, ∀ (a b R U U₁ G : ℝ) (f g : ℝ → ℝ) (nu : ℤ → ℝ),
      0 ≤ a → a < b → 0 < R → 1 ≤ U → 1 ≤ U₁ → 0 < G →
      AlgebraicOn f (Set.Icc a b) → AlgebraicOn g (Set.Icc a b) →
      ContDiff ℝ 3 f → ContDiff ℝ 1 g →
      (∀ t ∈ Set.Icc a b, c₁ / R ≤ iteratedDeriv 2 f t ∧ iteratedDeriv 2 f t ≤ c₂ / R) →
      (∀ t ∈ Set.Icc a b, |iteratedDeriv 3 f t| ≤ c₃ / (R * U)) →
      (∀ t ∈ Set.Icc a b, |g t| ≤ c₄ * G) →
      (∀ t ∈ Set.Icc a b, |deriv g t| ≤ c₅ * G / U₁) →
      (∀ u : ℤ, deriv f a ≤ u → (u : ℝ) ≤ deriv f b →
        nu u ∈ Set.Icc a b ∧ deriv f (nu u) = u) →
      ‖(∑ n ∈ intRange a b, (g n : ℂ) * e (f n)) -
          ∑ u ∈ Finset.Icc ⌈deriv f a⌉ ⌊deriv f b⌋,
            ((bWeight (deriv f a) (deriv f b) u * g (nu u) /
                Real.sqrt |iteratedDeriv 2 f (nu u)| : ℝ) : ℂ) *
              e (f (nu u) - u * nu u + 1 / 8)‖ ≤
        C * (G * Real.log (deriv f b - deriv f a + 2) +
              G * (b - a + R) * (U⁻¹ + U₁⁻¹) +
              G * minInv (Real.sqrt R) (angleBracket (deriv f a) (deriv f b) (deriv f a)) +
              G * minInv (Real.sqrt R) (angleBracket (deriv f a) (deriv f b) (deriv f b)))

/-- **Zhai–Cao, Lemma 8** (Srinivasan, Lemma 3).  For positive
`A_i, a_i, B_j, b_j` and `0 < Q₁ ≤ Q₂` there is `q ∈ [Q₁, Q₂]` with
`∑ A_i q^{a_i} + ∑ B_j q^{-b_j}
  ≤ 2^{m+n} (∑_i ∑_j (A_i^{b_j} B_j^{a_i})^{1/(a_i + b_j)} + ∑ A_i Q₁^{a_i} + ∑ B_j Q₂^{-b_j})`. -/
def zhaiCao_lemma8 : Prop :=
  ∀ (m n : ℕ) (A a : Fin m → ℝ) (B b : Fin n → ℝ) (Q₁ Q₂ : ℝ),
    (∀ i, 0 < A i) → (∀ i, 0 < a i) → (∀ j, 0 < B j) → (∀ j, 0 < b j) →
    0 < Q₁ → Q₁ ≤ Q₂ →
    ∃ q : ℝ, Q₁ ≤ q ∧ q ≤ Q₂ ∧
      ∑ i, A i * q ^ a i + ∑ j, B j * q ^ (-b j) ≤
        2 ^ (m + n) *
          (∑ i, ∑ j, (A i ^ b j * B j ^ a i) ^ (1 / (a i + b j)) +
            ∑ i, A i * Q₁ ^ a i + ∑ j, B j * Q₂ ^ (-b j))

/-! ### Wu, §2: multiple exponential sums with monomials -/

/-- The triple exponential sum of type I,
`S₁ = ∑_{h ∼ H} ∑_{m ∼ M} ∑_{n ∼ N} a_h b_m e(X h^α m^β n^γ / (H^α M^β N^γ))`. -/
noncomputable def tripleSumI (α β γ X H M N : ℝ) (a b : ℕ → ℂ) : ℂ :=
  ∑ h ∈ dyadic H, ∑ m ∈ dyadic M, ∑ n ∈ dyadic N,
    a h * b m *
      e (X * ((h : ℝ) ^ α * (m : ℝ) ^ β * (n : ℝ) ^ γ) / (H ^ α * M ^ β * N ^ γ))

/-- The triple exponential sum of type II,
`S₂ = ∑_{h ∼ H} ∑_{m ∼ M} ∑_{n ∼ N} a_h b_{m,n} e(X h^α m^β n^γ / (H^α M^β N^γ))`. -/
noncomputable def tripleSumII (α β γ X H M N : ℝ) (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) : ℂ :=
  ∑ h ∈ dyadic H, ∑ m ∈ dyadic M, ∑ n ∈ dyadic N,
    a h * b m n *
      e (X * ((h : ℝ) ^ α * (m : ℝ) ^ β * (n : ℝ) ^ γ) / (H ^ α * M ^ β * N ^ γ))

/-- The double exponential sum of type II,
`S₃ = ∑_{m ∼ M} ∑_{n ∼ N} a_m b_n e(X m^α n^β / (M^α N^β))`. -/
noncomputable def doubleSumII (α β X M N : ℝ) (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ dyadic M, ∑ n ∈ dyadic N,
    a m * b n * e (X * ((m : ℝ) ^ α * (n : ℝ) ^ β) / (M ^ α * N ^ β))

/-- `𝓛 = log(2 + X H M N)`. -/
noncomputable def logL (X H M N : ℝ) : ℝ := Real.log (2 + X * H * M * N)

/-- **Wu, Lemma 2.1** (Rivat–Sargos, Lemma 5).  If
`max_{j,k ≤ N} |x_j - x_k| ≤ 1 - 1/Q`, then
`|∑_{n ≤ N} z_n|² ≤ Q ∑_{j,k ≤ N, |x_j - x_k| ≤ 1/Q} (1 - Q |x_j - x_k|) z_j \bar z_k`
(the right-hand side is real; we take its real part). -/
def wu_lemma21 : Prop :=
  ∀ (N : ℕ) (Q : ℝ) (z : ℕ → ℂ) (x : ℕ → ℝ), 1 ≤ N → 1 ≤ Q →
    (∀ j ∈ Finset.Icc 1 N, ∀ k ∈ Finset.Icc 1 N, |x j - x k| ≤ 1 - 1 / Q) →
    ‖∑ n ∈ Finset.Icc 1 N, z n‖ ^ 2 ≤
      Q * (∑ j ∈ Finset.Icc 1 N, ∑ k ∈ (Finset.Icc 1 N).filter (fun k => |x j - x k| ≤ 1 / Q),
        ((1 - Q * |x j - x k| : ℝ) : ℂ) * z j * starRingEnd ℂ (z k)).re

/-- **Wu, Theorem 2** (a type I triple sum, after Rivat–Sargos).  Let
`k ≥ 2`, `K = 2^k`, `αβγ(1 - α) ≠ 0`, `(γ - 1)/(1 - α) ∉ {0, …, k - 1}`,
`|a_h|, |b_m| ≤ 1`.  If `X ≤ min(H², H² M⁻¹ N)` then
`S₁ ≪ {(X^K H^{4K-2k-4} M^{5K-k-8} N^{5K-3k-8})^{1/(6K-2k-8)} + (X H² M² N⁴)^{1/4}
       + (X H² M⁴ N²)^{1/4} + HM + H(MN)^{1/2} + H^{1/2} MN + X^{-1/2} HMN} 𝓛`. -/
def wu_theorem2 : Prop :=
  ∀ (k : ℕ) (α β γ : ℝ), 2 ≤ k → α * β * γ * (1 - α) ≠ 0 →
    (∀ j : ℕ, j < k → (γ - 1) / (1 - α) ≠ j) →
    ∃ C : ℝ, ∀ (X H M N : ℝ) (a b : ℕ → ℂ), 0 < X → 1 ≤ H → 1 ≤ M → 1 ≤ N →
      UnitBounded a → UnitBounded b → X ≤ H ^ 2 → X ≤ H ^ 2 * M⁻¹ * N →
      ‖tripleSumI α β γ X H M N a b‖ ≤
        C * ((X ^ (2 ^ k : ℝ) * H ^ (4 * 2 ^ k - 2 * k - 4 : ℝ) *
                M ^ (5 * 2 ^ k - k - 8 : ℝ) * N ^ (5 * 2 ^ k - 3 * k - 8 : ℝ)) ^
                (1 / (6 * 2 ^ k - 2 * k - 8 : ℝ)) +
              (X * H ^ 2 * M ^ 2 * N ^ 4) ^ ((1 : ℝ) / 4) +
              (X * H ^ 2 * M ^ 4 * N ^ 2) ^ ((1 : ℝ) / 4) +
              H * M + H * (M * N) ^ ((1 : ℝ) / 2) + H ^ ((1 : ℝ) / 2) * M * N +
              X ^ (-(1 : ℝ) / 2) * H * M * N) * logL X H M N

/-- **Wu, Lemma 2.5** (Sargos–Wu, (6.8), corrected).  For
`αβγ(γ-1)(γ-2)(α+γ-1)(α+2γ-2) ≠ 0` and `|a_h|, |b_m| ≤ 1`,
`S₁ ≪ {(X⁶ H²² M²² N¹¹)^{1/26} + (X H³ M³ N²)^{1/4} + (X² H³ M³)^{1/4}
       + (X² H¹⁸ M¹⁸ N⁷)^{1/18} + X⁻¹ HMN} 𝓛²`. -/
def wu_lemma25 : Prop :=
  ∀ α β γ : ℝ,
    α * β * γ * (γ - 1) * (γ - 2) * (α + γ - 1) * (α + 2 * γ - 2) ≠ 0 →
    ∃ C : ℝ, ∀ (X H M N : ℝ) (a b : ℕ → ℂ), 0 < X → 1 ≤ H → 1 ≤ M → 1 ≤ N →
      UnitBounded a → UnitBounded b →
      ‖tripleSumI α β γ X H M N a b‖ ≤
        C * ((X ^ 6 * H ^ 22 * M ^ 22 * N ^ 11) ^ ((1 : ℝ) / 26) +
              (X * H ^ 3 * M ^ 3 * N ^ 2) ^ ((1 : ℝ) / 4) +
              (X ^ 2 * H ^ 3 * M ^ 3) ^ ((1 : ℝ) / 4) +
              (X ^ 2 * H ^ 18 * M ^ 18 * N ^ 7) ^ ((1 : ℝ) / 18) +
              X⁻¹ * H * M * N) * logL X H M N ^ 2

/-- The Graham–Kolesnik function class `F(N, P, s, y, ε)` (Graham–Kolesnik,
*Van der Corput's Method of Exponential Sums*, §3.3): `f` has `P` continuous
derivatives (here: is `C^P` on `ℝ`), `[a, b] ⊆ [N, 2N]`, and for `0 ≤ p < P`
and `t ∈ [a, b]`,
`|f^{(p+1)}(t) - (-1)^p (s)_p y t^{-s-p}| < ε (s)_p y t^{-s-p}`, where
`(s)_p = s(s+1)⋯(s+p-1)` (so `f' ≈ y t^{-s}`). -/
def InGKClass (N : ℝ) (P : ℕ) (s y ε a b : ℝ) (f : ℝ → ℝ) : Prop :=
  N ≤ a ∧ a ≤ b ∧ b ≤ 2 * N ∧ ContDiff ℝ P f ∧
    ∀ p : ℕ, p < P → ∀ t ∈ Set.Icc a b,
      |iteratedDeriv (p + 1) f t -
          (-1) ^ p * (∏ i ∈ Finset.range p, (s + i)) * y * t ^ (-s - p)| <
        ε * (∏ i ∈ Finset.range p, (s + i)) * y * t ^ (-s - p)

/-- `(κ, l)` is an **exponent pair** (Graham–Kolesnik, §3.3, Definition):
`0 ≤ κ ≤ 1/2 ≤ l ≤ 1` and for every `s > 0` there are `P`, `ε ∈ (0, 1/2)` and
a constant `C` such that for all `N > 0`, `y > 0` and `f ∈ F(N, P, s, y, ε)`,
`|∑_{a < n ≤ b} e(f(n))| ≤ C ((y N^{-s})^κ N^l + y⁻¹ N^s)`. -/
def IsExponentPair (κ l : ℝ) : Prop :=
  0 ≤ κ ∧ κ ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 ∧
    ∀ s : ℝ, 0 < s → ∃ (P : ℕ) (ε C : ℝ), 0 < ε ∧ ε < 1 / 2 ∧
      ∀ (N y a b : ℝ) (f : ℝ → ℝ), 0 < N → 0 < y → InGKClass N P s y ε a b f →
        ‖∑ n ∈ intRange a b, e (f n)‖ ≤ C * ((y * N ^ (-s)) ^ κ * N ^ l + y⁻¹ * N ^ s)

/-- **Wu, Lemma 2.6, (2.14)** (Sargos–Wu, Theorem 7).  For `α < 1`,
`αβγ ≠ 0`, `|a_h|, |b_{m,n}| ≤ 1`,
`S₂ ≪ {(X⁴ H¹⁵ M²² N²²)^{1/26} + (X H² M³ N³)^{1/4} + H(MN)^{3/4} + H^{11/18} MN + X^{-1/2} HMN} 𝓛²`. -/
def wu_lemma26_eq214 : Prop :=
  ∀ α β γ : ℝ, α < 1 → α * β * γ ≠ 0 →
    ∃ C : ℝ, ∀ (X H M N : ℝ) (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ), 0 < X → 1 ≤ H → 1 ≤ M → 1 ≤ N →
      UnitBounded a → UnitBounded₂ b →
      ‖tripleSumII α β γ X H M N a b‖ ≤
        C * ((X ^ 4 * H ^ 15 * M ^ 22 * N ^ 22) ^ ((1 : ℝ) / 26) +
              (X * H ^ 2 * M ^ 3 * N ^ 3) ^ ((1 : ℝ) / 4) +
              H * (M * N) ^ ((3 : ℝ) / 4) + H ^ ((11 : ℝ) / 18) * M * N +
              X ^ (-(1 : ℝ) / 2) * H * M * N) * logL X H M N ^ 2

/-- **Wu, Lemma 2.6, (2.15)** (Liu–Wu, (3.11)).  For `α < 1`, `αβγ ≠ 0`,
`|a_h|, |b_{m,n}| ≤ 1` and an exponent pair `(κ, λ)`,
`S₂ ≪ {(X^κ H^{1+κ+λ} M^{2+κ} N^{2+κ})^{1/(2+2κ)} + H(MN)^{1/2} + H^{1/2} MN + X^{-1/2} HMN} 𝓛`. -/
def wu_lemma26_eq215 : Prop :=
  ∀ α β γ κ lam : ℝ, α < 1 → α * β * γ ≠ 0 → IsExponentPair κ lam →
    ∃ C : ℝ, ∀ (X H M N : ℝ) (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ), 0 < X → 1 ≤ H → 1 ≤ M → 1 ≤ N →
      UnitBounded a → UnitBounded₂ b →
      ‖tripleSumII α β γ X H M N a b‖ ≤
        C * ((X ^ κ * H ^ (1 + κ + lam) * M ^ (2 + κ) * N ^ (2 + κ)) ^ (1 / (2 + 2 * κ)) +
              H * (M * N) ^ ((1 : ℝ) / 2) + H ^ ((1 : ℝ) / 2) * M * N +
              X ^ (-(1 : ℝ) / 2) * H * M * N) * logL X H M N

/-- **Wu, Lemma 2.7, (2.16)** (from Wu 1998, (2.2)).  For
`αβ(α-1)(β-1) ≠ 0`, `|a_m|, |b_n| ≤ 1` and `X ≥ N`,
`S₃ ≪ {(X M³ N⁴)^{1/5} + (X⁴ M¹⁰ N¹¹)^{1/16} + (X M⁷ N¹⁰)^{1/11} + M N^{1/2}} 𝓛²`. -/
def wu_lemma27_eq216 : Prop :=
  ∀ α β : ℝ, α * β * (α - 1) * (β - 1) ≠ 0 →
    ∃ C : ℝ, ∀ (X M N : ℝ) (a b : ℕ → ℂ), 0 < X → 1 ≤ M → 1 ≤ N →
      UnitBounded a → UnitBounded b → N ≤ X →
      ‖doubleSumII α β X M N a b‖ ≤
        C * ((X * M ^ 3 * N ^ 4) ^ ((1 : ℝ) / 5) +
              (X ^ 4 * M ^ 10 * N ^ 11) ^ ((1 : ℝ) / 16) +
              (X * M ^ 7 * N ^ 10) ^ ((1 : ℝ) / 11) +
              M * N ^ ((1 : ℝ) / 2)) * logL X 1 M N ^ 2

/-- **Wu, Lemma 2.7, (2.17)** (from Wu 1998, (2.1) with `(κ, λ) = (1/2, 1/2)`).
Under the hypotheses of (2.16),
`S₃ ≪ {(X⁴ M¹³ N¹⁵)^{1/20} + (X³ M¹² N¹⁴)^{1/18} + (X M³ N⁴)^{1/5} + (X M⁷ N¹⁰)^{1/11} + M N^{1/2}} 𝓛²`. -/
def wu_lemma27_eq217 : Prop :=
  ∀ α β : ℝ, α * β * (α - 1) * (β - 1) ≠ 0 →
    ∃ C : ℝ, ∀ (X M N : ℝ) (a b : ℕ → ℂ), 0 < X → 1 ≤ M → 1 ≤ N →
      UnitBounded a → UnitBounded b → N ≤ X →
      ‖doubleSumII α β X M N a b‖ ≤
        C * ((X ^ 4 * M ^ 13 * N ^ 15) ^ ((1 : ℝ) / 20) +
              (X ^ 3 * M ^ 12 * N ^ 14) ^ ((1 : ℝ) / 18) +
              (X * M ^ 3 * N ^ 4) ^ ((1 : ℝ) / 5) +
              (X * M ^ 7 * N ^ 10) ^ ((1 : ℝ) / 11) +
              M * N ^ ((1 : ℝ) / 2)) * logL X 1 M N ^ 2

/-- **Wu, Lemma 2.7, (2.18)** (from Liu–Wu, Theorem 2).  For
`β(β-1) ≠ 0`, `α = 1/2`, `|a_m|, |b_n| ≤ 1` and `X ≥ max(M, N)`,
`S₃ ≪ {(X⁴ M¹⁰ N¹¹)^{1/16} + (X² M⁸ N⁹)^{1/12} + (X² M⁴ N³)^{1/6} + (X M² N³)^{1/4}} 𝓛²`. -/
def wu_lemma27_eq218 : Prop :=
  ∀ β : ℝ, β * (β - 1) ≠ 0 →
    ∃ C : ℝ, ∀ (X M N : ℝ) (a b : ℕ → ℂ), 0 < X → 1 ≤ M → 1 ≤ N →
      UnitBounded a → UnitBounded b → M ≤ X → N ≤ X →
      ‖doubleSumII (1 / 2) β X M N a b‖ ≤
        C * ((X ^ 4 * M ^ 10 * N ^ 11) ^ ((1 : ℝ) / 16) +
              (X ^ 2 * M ^ 8 * N ^ 9) ^ ((1 : ℝ) / 12) +
              (X ^ 2 * M ^ 4 * N ^ 3) ^ ((1 : ℝ) / 6) +
              (X * M ^ 2 * N ^ 3) ^ ((1 : ℝ) / 4)) * logL X 1 M N ^ 2

end LeanProofs.IntegerPoints
