import IntegerPoints.ExponentialSums
import IntegerPoints.AProcessTheorem

/-!
# Graham–Kolesnik, Chapter 3: formal statements

Formal statements (no proofs) of every numbered result of Graham–Kolesnik,
*Van der Corput's Method of Exponential Sums*, Chapter 3 ("The method of
exponent pairs"; OCR source `NumberTheory/IntegerPoints/Papers/The method of
exponent pairs.tex`) that is not already formalised elsewhere in this library:

* the class `F(N, P, s, y, ε)` is `InGKClass` and the definition of exponent
  pair is `IsExponentPair` (`IntegerPoints.ExponentialSums`);
* Lemma 3.7 is `gk_lemma37_holds`, built from `AP.lemma37_sharp`, and
  Theorem 3.8 is `AP.isExponentPair_A` (`IntegerPoints.GKLemma37`,
  `IntegerPoints.AProcess`, `IntegerPoints.AProcessTheorem`).

Stated here: the exponential-integral Lemmas 3.1–3.6 of §3.2 (including the
stationary-phase Lemma 3.4 with its explicit error terms `R₁`, `R₂`, and the
Poisson-summation Lemma 3.6 with its explicit main term), Lemma 3.9 and
Theorem 3.10 (the `B`-process) of §3.5, the results quoted from Chapter 2 in
the form in which the chapter invokes them (Theorems 2.1, 2.2, the
Weyl–van der Corput inequality (2.3.4), Theorem 2 of Appendix A), and the
unnumbered but substantive claims of §3.3 on the necessary shape of an
exponent pair.  Each statement is a `Prop`-valued definition, so this module
asserts nothing.

## Conventions

The conventions of `IntegerPoints.ExponentialSums` are used throughout:
`A ≪ B` with implied constant depending on parameters `p` is
`∀ p, ∃ C, ∀ (everything else), ‖A‖ ≤ C * B`; `≍`/`≈` hypotheses carry
explicit constants `c₁, c₂, …` quantified before `C`; functions of a real
variable are globally `C^k` on `ℝ` with hypotheses imposed on the interval in
question; sums `∑_{a < n ≤ b}` are over `intRange a b` (so `0 ≤ a` is
assumed); sums over integers `α ≤ ν ≤ β` are over `Finset.Icc ⌈α⌉ ⌊β⌋ : Finset ℤ`;
`∫ x in a..b, …` is the interval integral.  The quantity
`min(1/(λ₂ (x₀ - a)), λ₂^{-1/2})` of Lemma 3.4, read as `λ₂^{-1/2}` when
`x₀ = a`, is written with `minInv` (which handles Lean's `1/0 = 0`).
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

/-! ### §3.2 Lemmas on exponential integrals -/

/-- **Graham–Kolesnik, Lemma 3.1** (first-derivative test for integrals).  If
`f, g` are twice differentiable on `[a, b]`, `g/f'` is monotonic there and
`|f'(x)/g(x)| ≥ λ`, then `∫_a^b g(x) e(f(x)) dx ≪ 1/λ` (absolute constant).
We require `f' ≠ 0` on `[a, b]` so that `g/f'` is meaningful, and write
`|f'/g| ≥ λ` as `λ |g| ≤ |f'|`. -/
def gk_lemma31 : Prop :=
  ∃ C : ℝ, ∀ (a b lam : ℝ) (f g : ℝ → ℝ), a ≤ b → 0 < lam →
    ContDiff ℝ 2 f → ContDiff ℝ 2 g →
    (MonotoneOn (fun x => g x / deriv f x) (Set.Icc a b) ∨
      AntitoneOn (fun x => g x / deriv f x) (Set.Icc a b)) →
    (∀ x ∈ Set.Icc a b, deriv f x ≠ 0 ∧ lam * |g x| ≤ |deriv f x|) →
    ‖∫ x in a..b, (g x : ℂ) * e (f x)‖ ≤ C / lam

/-- **Graham–Kolesnik, Lemma 3.2** (second-derivative test for integrals).
If `f` has two continuous derivatives on `[a, b]` and `|f''| ≥ λ₂ > 0` there,
then `∫_a^b e(f(x)) dx ≪ λ₂^{-1/2}` (absolute constant). -/
def gk_lemma32 : Prop :=
  ∃ C : ℝ, ∀ (a b lam₂ : ℝ) (f : ℝ → ℝ), a ≤ b → 0 < lam₂ → ContDiff ℝ 2 f →
    (∀ x ∈ Set.Icc a b, lam₂ ≤ |iteratedDeriv 2 f x|) →
    ‖∫ x in a..b, e (f x)‖ ≤ C * lam₂ ^ (-(1 : ℝ) / 2)

/-- **Graham–Kolesnik, Lemma 3.3** (the Fresnel integral).  For `A, X > 0`,
`∫_{-X}^{X} e(A x²) dx = e(1/8) / √(2A) + O(1/(AX))` (absolute constant). -/
def gk_lemma33 : Prop :=
  ∃ C : ℝ, ∀ A X : ℝ, 0 < A → 0 < X →
    ‖(∫ x in (-X)..X, e (A * x ^ 2)) - e (1 / 8) / ((Real.sqrt (2 * A) : ℝ) : ℂ)‖ ≤
      C / (A * X)

/-- The error term `R₁ = min(1/(λ₂(x₀ - a)), λ₂^{-1/2}) + min(1/(λ₂(b - x₀)), λ₂^{-1/2})`
of Lemma 3.4, with the convention `1/0 = +∞` at `x₀ = a` or `x₀ = b`. -/
noncomputable def gkR₁ (lam₂ a b x₀ : ℝ) : ℝ :=
  minInv (lam₂ ^ (-(1 : ℝ) / 2)) (lam₂ * (x₀ - a)) +
    minInv (lam₂ ^ (-(1 : ℝ) / 2)) (lam₂ * (b - x₀))

/-- The error term `R₂ = (b - a) λ₄ λ₂⁻² + (b - a) λ₃² λ₂⁻³` of Lemma 3.4. -/
noncomputable def gkR₂ (lam₂ lam₃ lam₄ a b : ℝ) : ℝ :=
  (b - a) * lam₄ * lam₂ ^ (-(2 : ℝ)) + (b - a) * lam₃ ^ 2 * lam₂ ^ (-(3 : ℝ))

/-- **Graham–Kolesnik, Lemma 3.4** (stationary phase), the case `g'' ≥ λ₂ > 0`.
Suppose `g` is real-valued with four continuous derivatives on `[a, b]`,
`g''(x) ≥ λ₂ > 0`, `g'(x₀) = 0` for some `x₀ ∈ [a, b]`, and
`|g'''| ≤ λ₃`, `|g''''| ≤ λ₄` on `[a, b]`.  Then
`∫_a^b e(g(x)) dx = e(1/8 + g(x₀)) / g''(x₀)^{1/2} + O(R₁ + R₂)` (3.2.1),
with `R₁ = gkR₁ λ₂ a b x₀`, `R₂ = gkR₂ λ₂ λ₃ λ₄ a b` and an absolute implied
constant. -/
def gk_lemma34 : Prop :=
  ∃ C : ℝ, ∀ (a b x₀ lam₂ lam₃ lam₄ : ℝ) (g : ℝ → ℝ),
    a ≤ b → 0 < lam₂ → 0 < lam₃ → 0 < lam₄ → ContDiff ℝ 4 g →
    (∀ x ∈ Set.Icc a b, lam₂ ≤ iteratedDeriv 2 g x) →
    x₀ ∈ Set.Icc a b → deriv g x₀ = 0 →
    (∀ x ∈ Set.Icc a b, |iteratedDeriv 3 g x| ≤ lam₃) →
    (∀ x ∈ Set.Icc a b, |iteratedDeriv 4 g x| ≤ lam₄) →
    ‖(∫ x in a..b, e (g x)) -
        e (1 / 8 + g x₀) / ((Real.sqrt (iteratedDeriv 2 g x₀) : ℝ) : ℂ)‖ ≤
      C * (gkR₁ lam₂ a b x₀ + gkR₂ lam₂ lam₃ lam₄ a b)

/-- **Graham–Kolesnik, Lemma 3.4**, the case `g'' ≤ -λ₂ < 0`: the same
statement with main term `e(-1/8 + g(x₀)) / |g''(x₀)|^{1/2}`. -/
def gk_lemma34_neg : Prop :=
  ∃ C : ℝ, ∀ (a b x₀ lam₂ lam₃ lam₄ : ℝ) (g : ℝ → ℝ),
    a ≤ b → 0 < lam₂ → 0 < lam₃ → 0 < lam₄ → ContDiff ℝ 4 g →
    (∀ x ∈ Set.Icc a b, iteratedDeriv 2 g x ≤ -lam₂) →
    x₀ ∈ Set.Icc a b → deriv g x₀ = 0 →
    (∀ x ∈ Set.Icc a b, |iteratedDeriv 3 g x| ≤ lam₃) →
    (∀ x ∈ Set.Icc a b, |iteratedDeriv 4 g x| ≤ lam₄) →
    ‖(∫ x in a..b, e (g x)) -
        e (-1 / 8 + g x₀) / ((Real.sqrt |iteratedDeriv 2 g x₀| : ℝ) : ℂ)‖ ≤
      C * (gkR₁ lam₂ a b x₀ + gkR₂ lam₂ lam₃ lam₄ a b)

/-- **Graham–Kolesnik, Lemma 3.5** (truncated Poisson summation).  Suppose
`f` has two continuous derivatives on `[a, b]`, `f'` is decreasing, `H₁, H₂`
are integers with `H₁ < f'(x) < H₂` on `[a, b]`, and `H = H₂ - H₁ ≥ 2`.  Then
`∑_{a < n ≤ b} e(f(n)) = ∑_{H₁ ≤ h ≤ H₂} ∫_a^b e(f(x) - h x) dx + O(log H)`
(absolute constant). -/
def gk_lemma35 : Prop :=
  ∃ C : ℝ, ∀ (a b : ℝ) (H₁ H₂ : ℤ) (f : ℝ → ℝ), 0 ≤ a → a ≤ b → ContDiff ℝ 2 f →
    AntitoneOn (deriv f) (Set.Icc a b) →
    (∀ x ∈ Set.Icc a b, (H₁ : ℝ) < deriv f x ∧ deriv f x < H₂) →
    H₁ + 2 ≤ H₂ →
    ‖(∑ n ∈ intRange a b, e (f n)) -
        ∑ h ∈ Finset.Icc H₁ H₂, ∫ x in a..b, e (f x - (h : ℝ) * x)‖ ≤
      C * Real.log ((H₂ : ℝ) - H₁)

/-- **Graham–Kolesnik, Lemma 3.6** (the `B`-process transformation).  Suppose
`f` has four continuous derivatives on `[a, b] ⊆ [N, 2N]`, `f'' < 0` there,
and for some `F > 0`
`-f'' ≍ F N⁻²`, `f''' ≪ F N⁻³`, `f'''' ≪ F N⁻⁴` on `[a, b]`.  Let
`α = f'(b)`, `β = f'(a)`, let `x_ν ∈ [a, b]` solve `f'(x_ν) = ν` for
`ν ∈ [α, β]`, and `φ(ν) = -f(x_ν) + ν x_ν`.  Then
`∑_{a < n ≤ b} e(f(n))
   = ∑_{α ≤ ν ≤ β} e(-φ(ν) - 1/8) / |f''(x_ν)|^{1/2}
     + O(log(F N⁻¹ + 2) + F^{-1/2} N)`,
the implied constant depending only on the `≍`/`≪` constants.  (Here
`-φ(ν) = f(x_ν) - ν x_ν`.) -/
def gk_lemma36 : Prop :=
  ∀ c₁ c₂ c₃ c₄ : ℝ, 0 < c₁ → 0 < c₂ → 0 < c₃ → 0 < c₄ →
    ∃ C : ℝ, ∀ (N F a b : ℝ) (f : ℝ → ℝ) (xν : ℤ → ℝ),
      0 < N → 0 < F → N ≤ a → a ≤ b → b ≤ 2 * N → ContDiff ℝ 4 f →
      (∀ t ∈ Set.Icc a b,
        c₁ * F * N ^ (-(2 : ℝ)) ≤ -iteratedDeriv 2 f t ∧
          -iteratedDeriv 2 f t ≤ c₂ * F * N ^ (-(2 : ℝ))) →
      (∀ t ∈ Set.Icc a b, |iteratedDeriv 3 f t| ≤ c₃ * F * N ^ (-(3 : ℝ))) →
      (∀ t ∈ Set.Icc a b, |iteratedDeriv 4 f t| ≤ c₄ * F * N ^ (-(4 : ℝ))) →
      (∀ ν : ℤ, deriv f b ≤ ν → (ν : ℝ) ≤ deriv f a →
        xν ν ∈ Set.Icc a b ∧ deriv f (xν ν) = ν) →
      ‖(∑ n ∈ intRange a b, e (f n)) -
          ∑ ν ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
            e (f (xν ν) - (ν : ℝ) * xν ν - 1 / 8) /
              ((Real.sqrt |iteratedDeriv 2 f (xν ν)| : ℝ) : ℂ)‖ ≤
        C * (Real.log (F * N⁻¹ + 2) + F ^ (-(1 : ℝ) / 2) * N)

/-! ### Results quoted from Chapter 2, in the form in which §3.3–§3.4 invoke them -/

/-- **Graham–Kolesnik, Theorem 2.1** (Kuz'min–Landau), as invoked in §3.3:
for `f ∈ F(N, 2, s, y, ε)` with `y N^{-s} < 1/2`,
`|∑_{a < n ≤ b} e(f(n))| ≪ y⁻¹ N^s`, the constant depending on `s, ε`.
(Theorem 2.1 needs `f'` monotonic, which (3.3.3) provides only through the
`p = 1` condition `f'' ≈ -s y t^{-s-1} < 0`; with `P = 1` the class imposes
nothing on `f''` and the bound is false, so `P = 2` is the form in which the
remark of §3.3 actually invokes the theorem.) -/
def gk_theorem21_invoked : Prop :=
  ∀ s ε : ℝ, 0 < s → 0 < ε → ε < 1 / 2 →
    ∃ C : ℝ, ∀ (N y a b : ℝ) (f : ℝ → ℝ), 0 < N → 0 < y →
      InGKClass N 2 s y ε a b f → y * N ^ (-s) < 1 / 2 →
      ‖∑ n ∈ intRange a b, e (f n)‖ ≤ C * (y⁻¹ * N ^ s)

/-- **Graham–Kolesnik, Theorem 2.2** (van der Corput's second-derivative
test), as invoked in §3.3: for `f ∈ F(N, 2, s, y, ε)` with
`1/2 ≤ y N^{-s} < 1`, `|∑_{a < n ≤ b} e(f(n))| ≪ N^{1/2}`. -/
def gk_theorem22_invoked_sec33 : Prop :=
  ∀ s ε : ℝ, 0 < s → 0 < ε → ε < 1 / 2 →
    ∃ C : ℝ, ∀ (N y a b : ℝ) (f : ℝ → ℝ), 0 < N → 0 < y →
      InGKClass N 2 s y ε a b f → 1 / 2 ≤ y * N ^ (-s) → y * N ^ (-s) < 1 →
      ‖∑ n ∈ intRange a b, e (f n)‖ ≤ C * N ^ ((1 : ℝ) / 2)

/-- **Graham–Kolesnik, Theorem 2.2**, as invoked in the proof of Theorem 3.8:
for `f ∈ F(N, 2, s, y, ε)` with `1 ≤ L = y N^{-s} < log N`,
`|∑_{a < n ≤ b} e(f(n))| ≪ N^{1/2} (log N)^{1/2}`. -/
def gk_theorem22_invoked_sec34 : Prop :=
  ∀ s ε : ℝ, 0 < s → 0 < ε → ε < 1 / 2 →
    ∃ C : ℝ, ∀ (N y a b : ℝ) (f : ℝ → ℝ), 0 < N → 0 < y →
      InGKClass N 2 s y ε a b f → 1 ≤ y * N ^ (-s) → y * N ^ (-s) < Real.log N →
      ‖∑ n ∈ intRange a b, e (f n)‖ ≤
        C * (N ^ ((1 : ℝ) / 2) * (Real.log N) ^ ((1 : ℝ) / 2))

/-- **Graham–Kolesnik, (2.3.4)** (the Weyl–van der Corput inequality), as
stated in §3.3: for `I = (a, b] ⊆ [N, 2N]` and an integer `1 ≤ H ≤ N`,
`|S|² ≪ N²/H + (N/H) ∑_{1 ≤ h ≤ H} |S₁(h)|`, where
`S₁(h) = ∑_{a < n ≤ b, a < n + h ≤ b} e(f(n) - f(n + h))` (3.3.1) and the
implied constant is absolute. -/
def gk_eq234 : Prop :=
  ∃ C : ℝ, ∀ (N a b : ℝ) (H : ℕ) (f : ℝ → ℝ), 0 < N → N ≤ a → a ≤ b → b ≤ 2 * N →
    1 ≤ H → (H : ℝ) ≤ N →
    ‖∑ n ∈ intRange a b, e (f n)‖ ^ 2 ≤
      C * (N ^ 2 / H + (N / H) * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ intRange a (b - h), e (f n - f (n + h))‖)

/-- **Graham–Kolesnik, Appendix A, Theorem 2**, as invoked in §3.3: for a
positive integer `N`, `S(t) = ∑_{N < n ≤ 2N} e(t/n)` satisfies
`∫_T^{2T} |S(t)|² dt ≥ (T - 4N²) N`. -/
def gk_appendixA_theorem2_invoked : Prop :=
  ∀ (N : ℕ) (T : ℝ), 0 < N → 0 < T →
    (T - 4 * (N : ℝ) ^ 2) * N ≤
      ∫ t in T..(2 * T), ‖∑ n ∈ intRange (N : ℝ) (2 * (N : ℝ)), e (t / n)‖ ^ 2

/-! ### §3.3: the shape of an exponent pair -/

/-- The estimate (3.3.4) alone, without the side conditions
`0 ≤ k ≤ 1/2 ≤ l ≤ 1`: for every `s > 0` there are `P`, `ε ∈ (0, 1/2)` and
`C` with `|∑_{a < n ≤ b} e(f(n))| ≤ C ((y N^{-s})^k N^l + y⁻¹ N^s)` for all
`f ∈ F(N, P, s, y, ε)`.  Thus
`IsExponentPair k l ↔ 0 ≤ k ≤ 1/2 ≤ l ≤ 1 ∧ SatisfiesExponentPairBound k l`. -/
def SatisfiesExponentPairBound (k l : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ∃ (P : ℕ) (ε C : ℝ), 0 < ε ∧ ε < 1 / 2 ∧
    ∀ (N y a b : ℝ) (f : ℝ → ℝ), 0 < N → 0 < y → InGKClass N P s y ε a b f →
      ‖∑ n ∈ intRange a b, e (f n)‖ ≤ C * ((y * N ^ (-s)) ^ k * N ^ l + y⁻¹ * N ^ s)

/-- **Graham–Kolesnik, §3.3** (remark): no pair `(k, l)` satisfying (3.3.4)
has `l < 1/2` (via `S(t) = ∑_{N < n ≤ 2N} e(t/n)` and Appendix A). -/
def gk_sec33_l_ge_half : Prop :=
  ∀ k l : ℝ, SatisfiesExponentPairBound k l → 1 / 2 ≤ l

/-- **Graham–Kolesnik, §3.3** (remark): no pair `(k, l)` satisfying (3.3.4)
has `k < 0`, and if `k = 0` then `l ≥ 1` (via `t_ν = ν lcm{1, …, 2N}`, for
which `S(t_ν) = N`). -/
def gk_sec33_k_nonneg : Prop :=
  ∀ k l : ℝ, SatisfiesExponentPairBound k l → 0 ≤ k ∧ (k = 0 → 1 ≤ l)

/-- **Graham–Kolesnik, §3.3** (remark): if `(k, 1/2)` is an exponent pair
then `k = 1/2` (via `f(x) = 2 t x^{1/2}`, `t² = lcm{1, …, H}`, and
Lemma 3.6). -/
def gk_sec33_k_eq_half_of_l_eq_half : Prop :=
  ∀ k : ℝ, IsExponentPair k (1 / 2) → k = 1 / 2

/-! ### §3.4 Lemma 3.7 in the book's form -/

/-- **Graham–Kolesnik, Lemma 3.7** (the book's form, proved as
`gk_lemma37_holds`).  If `P ≥ 1`,
`f ∈ F(N, P, s, y, ε)` on `[a, b]` and `1 ≤ h < min(b - a, 2εN/(s+P))`, then
`f₁(x) = f(x) - f(x + h)` lies in `F(N, P - 1, s + 1, s h y, 3ε)` on
`[a, b - h]`. -/
def gk_lemma37 : Prop :=
  ∀ (N : ℝ) (P : ℕ) (s y ε a b h : ℝ) (f : ℝ → ℝ),
    1 ≤ P → 0 < s → 0 < y → 0 < ε → ε < 1 / 2 →
    InGKClass N P s y ε a b f →
    1 ≤ h → h < b - a → h < 2 * ε * N / (s + P) →
    InGKClass N (P - 1) (s + 1) (s * h * y) (3 * ε) a (b - h) (fun x => f x - f (x + h))

/-! ### §3.5 The `B`-process -/

/-- **Graham–Kolesnik, Lemma 3.9**.  Suppose `P ≥ 2`, `f ∈ F(N, P, s, y, ε)`
on `[a, b]`, `α = f'(b)`, `β = f'(a)`; for `ν ∈ [α, β]` let `x_ν ∈ [a, b]`
solve `f'(x_ν) = ν` and put `φ(ν) = ν x_ν - f(x_ν)`.  Let `σ = 1/s` and
`η = y^σ`.  Then there is `C = C(s, P)` such that
`|φ^{(p+1)}(ν) - (-1)^p (σ)_p η ν^{-σ-p}| < C ε (σ)_p η ν^{-σ-p}`
for `0 ≤ p ≤ P - 1` and `α ≤ ν ≤ β`.  The inverse function `x` (determined
on `[α, β]` by `f'(x_ν) = ν`, since `f'` is strictly decreasing there; it is
only `C^{P-1}`, so no regularity is imposed on it) and `φ`, quantified as a
globally `C^P` function on `ℝ`, agree with the book's `x_ν`, `φ(ν)` on
`[α, β]`.  The interval is required to be nondegenerate: if `a = b`, the
displayed value identities constrain `φ` at only one point and cannot imply
anything about its derivatives there. -/
def gk_lemma39 : Prop :=
  ∀ (s : ℝ) (P : ℕ), 0 < s → 2 ≤ P →
    ∃ C : ℝ, ∀ (N y ε a b : ℝ) (f x φ : ℝ → ℝ), 0 < N → 0 < y → 0 < ε → ε < 1 / 2 →
      InGKClass N P s y ε a b f →
      a < b →
      ContDiff ℝ P φ →
      (∀ ν ∈ Set.Icc (deriv f b) (deriv f a), x ν ∈ Set.Icc a b ∧ deriv f (x ν) = ν) →
      (∀ ν ∈ Set.Icc (deriv f b) (deriv f a), φ ν = ν * x ν - f (x ν)) →
      ∀ p : ℕ, p < P → ∀ ν ∈ Set.Icc (deriv f b) (deriv f a),
        |iteratedDeriv (p + 1) φ ν -
            (-1) ^ p * (∏ i ∈ Finset.range p, (1 / s + i)) * y ^ (1 / s) * ν ^ (-(1 / s) - p)| <
          C * ε * (∏ i ∈ Finset.range p, (1 / s + i)) * y ^ (1 / s) * ν ^ (-(1 / s) - p)

/-- **Graham–Kolesnik, §3.5** (the remark after Lemma 3.9, in terms of the
class `F`): under the hypotheses of Lemma 3.9, for every `J` with
`α ≤ J ≤ β` the restriction of `φ` to `[α, β] ∩ [J, 2J]` lies in
`F(J, P, σ, η, Cε)`.  As in Lemma 3.9, `a < b` is essential for the inverse
data to determine derivatives of `φ`. -/
def gk_lemma39_class : Prop :=
  ∀ (s : ℝ) (P : ℕ), 0 < s → 2 ≤ P →
    ∃ C : ℝ, ∀ (N y ε a b : ℝ) (f x φ : ℝ → ℝ), 0 < N → 0 < y → 0 < ε → ε < 1 / 2 →
      InGKClass N P s y ε a b f →
      a < b →
      ContDiff ℝ P φ →
      (∀ ν ∈ Set.Icc (deriv f b) (deriv f a), x ν ∈ Set.Icc a b ∧ deriv f (x ν) = ν) →
      (∀ ν ∈ Set.Icc (deriv f b) (deriv f a), φ ν = ν * x ν - f (x ν)) →
      ∀ J : ℝ, deriv f b ≤ J → J ≤ deriv f a →
        InGKClass J P (1 / s) (y ^ (1 / s)) (C * ε)
          (max (deriv f b) J) (min (deriv f a) (2 * J)) φ

/-- **Graham–Kolesnik, Theorem 3.10** (the `B`-process).  If `(k, l)` is an
exponent pair then so is `B(k, l) = (l - 1/2, k + 1/2)`. -/
def gk_theorem310 : Prop :=
  ∀ k l : ℝ, IsExponentPair k l → IsExponentPair (l - 1 / 2) (k + 1 / 2)

/-- **Graham–Kolesnik, §3.1** (consequence of Theorems 3.8 and 3.10): every
pair of the forms (3.1.2), (3.1.3) — obtained from `(0, 1)` by a finite word
in the processes `A` and `B` — is an exponent pair.  Words are lists of
booleans, `true` for `A` and `false` for `B`, applied right to left. -/
noncomputable def gk_process_word : List Bool → ℝ × ℝ → ℝ × ℝ
  | [], p => p
  | (true :: w), p =>
      let q := gk_process_word w p
      (q.1 / (2 * q.1 + 2), (q.1 + q.2 + 1) / (2 * q.1 + 2))
  | (false :: w), p =>
      let q := gk_process_word w p
      (q.2 - 1 / 2, q.1 + 1 / 2)

/-- **Graham–Kolesnik, §3.1**: all pairs `A^{q₁} B ⋯ A^{q_k} B (0, 1)` and
`B A^{q₁} B ⋯ A^{q_k} B (0, 1)` are exponent pairs; equivalently, every word in
`A`, `B` applied to `(0, 1)` gives an exponent pair. -/
def gk_sec31_words : Prop :=
  ∀ w : List Bool, IsExponentPair (gk_process_word w (0, 1)).1 (gk_process_word w (0, 1)).2

end LeanProofs.IntegerPoints
