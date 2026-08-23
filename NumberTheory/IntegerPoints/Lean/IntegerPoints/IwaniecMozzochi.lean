import IntegerPoints.ExponentialSums
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Iwaniec–Mozzochi, *On the divisor and circle problems*

Formal statements (no proofs) of the results of

> H. Iwaniec and C. J. Mozzochi, On the divisor and circle problems,
> J. Number Theory 29 (1988), 60–93,

transcribed in `Papers/On the divisor and circle problems.tex`.  Every
statement is a `Prop`-valued definition; nothing is asserted.

## Contents

* §1: `D(x)`, `Δ(x)`, the main theorems (1.1)/(1.2) and (1.5)/(1.8) with
  `θ = 7/22`, the Bombieri–Iwaniec bound (1.3), and the representation
  (1.6)/(1.7) of `R(x)` by the congruence divisor sums `D(x; k₁, l₁, k₂, l₂)`.
* §2–§3: `ψ`, `Δ(x, M)`, `ψ_H`, `Δ(x, H, M)` and the reductions (2.1), (3.2).
* §4: the exponent-pair bounds and the resulting restriction (4.1)/(4.2).
* §5–§6: Weyl's shift (5.1), the Farey set `𝓡` (6.1)/(6.2), the choices
  (6.4)/(6.5), the bound (6.6), the quantity `Δ(x, C, H, M)` of (6.11), and
  the decomposition (6.9) with the long-interval bound (7.6).
* §7: Poisson summation (7.2), the integral bounds (7.3)/(7.4), and (7.5).
* §8: the incomplete theta series and the approximation (8.4).
* §9: the approximate modular relation (9.6)/(9.7).
* §10: the Fourier integral `I(k, l)`, the representation (10.2) and the
  decay bound (10.6); the scales (10.3), (10.5), (10.7).
* §11: Lemma 11.1 ((11.2)–(11.4)), the Bessel integral (11.5), and (11.7).
* §12: the coefficients (12.2), the bilinear forms `𝓑_{t₁t₂}(𝐱; K, L)` and
  `𝓑(A, C, K, L)`, and (12.4).
* §13: Theorem 4.1 of Bombieri–Iwaniec (the count `𝒩(Δ₁, Δ₂; A, C)` of
  (13.10)/(13.11)), the bounds (13.12), (13.13), and the final estimates.
* §14: `𝓑(δ, K, L)`, the integral form (14.4), Theorem 14.1, the
  restricted count `𝓑*(δ, K, L)` of (14.6)/(14.7), its trivial bounds, the
  split (14.14) and the bounds (14.18) and for `𝓑₂(δ, K, L)`.

## Conventions

* `ψ(t) = {t} - 1/2` is `sawtooth`; `d(n)` is `(Nat.divisors n).card`;
  `γ` is `Real.eulerMascheroniConstant`.
* `m ∼ M` is the dyadic block `dyadic M = (M, 2M]` of `IntegerPoints.Basic`;
  the paper uses `[M, 2M)`, and the difference is immaterial for every
  statement below.  Where the paper writes `k ≍ K` in a definition, the
  dyadic block is used as well.
* `≪` is rendered with explicit constants; `x^ε`-losses are
  `∀ ε > 0, ∃ C`.  Absolute constants `μ₀, μ₁, …` of the paper that are
  "sufficiently small/large" are quantified before the implied constant.
* Smooth means `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`.  "Supported in
  `[u, v]`" is rendered as `∀ t, f t ≠ 0 → u ≤ t ∧ t ≤ v`.
* `θ = 7/22` throughout is `theta0`; `N = M x^{-2(1-θ)/5}` is
  `shiftLength x M`, `G = M³/(xNH)` is `Gscale x H M`, `A = x C M⁻²`,
  `K = x C N² M⁻³`, `L = x C H N M⁻³`.
* Sums over all integers of compactly supported summands are written with
  `finsum` (`∑ᶠ`); the Poisson-dual sums over `k ∈ ℤ` use `tsum` (`∑'`).
* The conditionally convergent Bessel integral (11.5) is stated as a limit
  of absolutely convergent integrals `∫_δ^∞` as `δ → 0⁺`.
* `ā` (the inverse of `a` modulo `c`) is `modInv a c = ((a : ZMod c)⁻¹).val`.
* `𝓕` is Mathlib's Fourier transform `𝓕 f (y) = ∫ f(t) e(-t y) dt`; the
  paper's convention differs by the sign of `y`, which does not affect
  `∫ y² |f̂(y)| dy`.
-/

open scoped BigOperators FourierTransform
open Real Finset Filter

namespace LeanProofs.IntegerPoints

/-! ### §1: the divisor problem and the circle problem -/

/-- `D(x) = ∑_{1 ≤ n ≤ x} d(n)`. -/
noncomputable def imDivisorSum (x : ℝ) : ℕ := ∑ n ∈ upTo x, (Nat.divisors n).card

/-- `Δ(x) = D(x) - x log x - (2γ - 1) x`. -/
noncomputable def imDivisorError (x : ℝ) : ℝ :=
  (imDivisorSum x : ℝ) - x * Real.log x - (2 * Real.eulerMascheroniConstant - 1) * x

/-- **(1.1)**: `Δ(x) ≪ x^{θ+ε}` for all `x ≥ 1` and `ε > 0`, the constant
depending only on `ε`. -/
def DivisorBound (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |imDivisorError x| ≤ C * x ^ (θ + ε)

/-- **(1.5)**: `P(x) ≪ x^{θ+ε}` for all `x ≥ 1` and `ε > 0`.  (The paper's
`P(x) = ∑_{1 ≤ n ≤ x} r(n) - πx` differs from `circleError x` by the term
`r(0) = 1`.) -/
def CircleBound (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |circleError x| ≤ C * x ^ (θ + ε)

/-- The exponent **(1.2)**/**(1.8)**, `θ = 7/22`. -/
noncomputable def theta0 : ℝ := 7 / 22

/-- **Iwaniec–Mozzochi, main theorem for the divisor problem**, (1.1) with
(1.2): `Δ(x) ≪ x^{7/22 + ε}`. -/
def iwaniecMozzochi_theorem_divisor : Prop := DivisorBound theta0

/-- **Iwaniec–Mozzochi, main theorem for the circle problem**, (1.5) with
(1.8): `P(x) ≪ x^{7/22 + ε}`. -/
def iwaniecMozzochi_theorem_circle : Prop := CircleBound theta0

/-- **(1.3)** (Bombieri–Iwaniec): `ζ(1/2 + it) ≪ t^{9/56 + ε}` for `t ≥ 1`. -/
def bombieriIwaniec_zetaBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
    ‖riemannZeta ((1 : ℂ) / 2 + Complex.I * t)‖ ≤ C * t ^ ((9 : ℝ) / 56 + ε)

open Classical in
/-- **(1.7)**: `D(x; k₁, l₁, k₂, l₂) = #{(n₁, n₂) : n₁ n₂ ≤ x, n_j ≡ l_j (mod k_j)}`
over positive integers `n₁, n₂`. -/
noncomputable def congruenceDivisorCount (x : ℝ) (k₁ l₁ k₂ l₂ : ℕ) : ℕ :=
  ((upTo x ×ˢ upTo x).filter fun p : ℕ × ℕ =>
    ((p.1 * p.2 : ℕ) : ℝ) ≤ x ∧ p.1 % k₁ = l₁ % k₁ ∧ p.2 % k₂ = l₂ % k₂).card

/-- **(1.6)**: `R(x) = 4 D(x; 4, 1, 1, 1) - 4 D(x; 4, 3, 1, 1)`, where
`R(x) = ∑_{1 ≤ n ≤ x} r(n) = latticeCount x - 1` (the point `(0, 0)` is
excluded). -/
def iwaniecMozzochi_eq16 : Prop :=
  ∀ x : ℝ, 0 ≤ x →
    (latticeCount x : ℝ) - 1 =
      4 * (congruenceDivisorCount x 4 1 1 1 : ℝ) - 4 * (congruenceDivisorCount x 4 3 1 1 : ℝ)

/-! ### §2: analytic formulation of `Δ(x)` -/

/-- `ψ(t) = {t} - 1/2`. -/
noncomputable def sawtooth (t : ℝ) : ℝ := Int.fract t - 1 / 2

/-- **§2, identity**: `Δ(x) = -2 ∑_{1 ≤ m < x^{1/2}} ψ(x/m) + O(1)`. -/
def iwaniecMozzochi_section2_identity : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    |imDivisorError x + 2 * ∑ m ∈ Finset.Ico 1 ⌈Real.sqrt x⌉₊, sawtooth (x / m)| ≤ C

/-- `Δ(x, M) = ∑_{m ∼ M} ψ(x/m)`. -/
noncomputable def deltaM (x M : ℝ) : ℝ := ∑ m ∈ dyadic M, sawtooth (x / m)

/-- **(2.1)** for the range **(2.2)**: `Δ(x, M) ≪ x^{θ+ε}` for
`x^θ < M < x^{1/2}`. -/
def DeltaMBound (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x M : ℝ, 1 ≤ x → x ^ θ < M → M < x ^ ((1 : ℝ) / 2) →
    |deltaM x M| ≤ C * x ^ (θ + ε)

/-- **(2.1)** with `θ = 7/22`. -/
def iwaniecMozzochi_eq21 : Prop := DeltaMBound theta0

/-- **§2, reduction**: since `|Δ(x, M)| ≤ M`, (2.1) on the range (2.2)
implies (1.1), for any `0 < θ < 1/2`. -/
def iwaniecMozzochi_reduction_eq21 : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 / 2 → DeltaMBound θ → DivisorBound θ

/-! ### §3: Fourier analysis of `Δ(x)` -/

/-- The smooth partition function `χ` of §3: `χ(t) = 0` for `t ≥ 4`,
`0 < χ(t) ≤ 1` for `2 ≤ t < 4`, `χ(t) = 1 - χ(2t)` for `1 < t ≤ 2`, and
`χ(t) = 0` for `t ≤ 1`. -/
def IsDyadicPartition (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
    (∀ t : ℝ, 4 ≤ t → χ t = 0) ∧
    (∀ t : ℝ, 2 ≤ t → t < 4 → 0 < χ t ∧ χ t ≤ 1) ∧
    (∀ t : ℝ, 1 < t → t ≤ 2 → χ t = 1 - χ (2 * t)) ∧
    (∀ t : ℝ, t ≤ 1 → χ t = 0)

/-- **(3.1)**: `∑_{H = 2^j, j ∈ ℤ} χ(x/H) = 1` for all `x > 0`. -/
def iwaniecMozzochi_eq31 : Prop :=
  ∀ χ : ℝ → ℝ, IsDyadicPartition χ → ∀ x : ℝ, 0 < x → ∑ᶠ j : ℤ, χ (x / (2 : ℝ) ^ j) = 1

/-- `ψ_H(t) = ∑_h χ(h/H) sin(2πht)/(πh)`. -/
noncomputable def psiH (χ : ℝ → ℝ) (H t : ℝ) : ℝ :=
  ∑ᶠ h : ℕ, χ (h / H) * Real.sin (2 * π * h * t) / (π * h)

/-- **§3, the Fourier expansion of `ψ`** (boundedly convergent):
`ψ(t) = -∑_{1 ≤ h ≤ y} (πh)⁻¹ sin(2πht) + O((1 + ‖t‖ y)⁻¹)`. -/
def sawtooth_fourierExpansion : Prop :=
  ∃ C : ℝ, ∀ t y : ℝ, 1 ≤ y →
    |sawtooth t + ∑ h ∈ upTo y, Real.sin (2 * π * h * t) / (π * h)| ≤
      C * (1 + nearestIntDist t * y)⁻¹

/-- **§3, partial summation**:
`ψ(t) = -ψ_{1/2}(t) - ∑_{1 ≤ H < y} ψ_H(t) + O((1 + ‖t‖ y)⁻¹)`,
with `H = 2^j`, `j : ℕ`, in the sum.

The separate `H = 1/2` block is forced by the partition (3.1): its `h = 1`
term has weight `χ(2) = 1`, whereas the first block indexed by `j : ℕ` has
`H = 1` and weight `χ(1) = 0` at `h = 1`.  Thus omitting `ψ_{1/2}` loses the
first Fourier mode.  The sign follows from `sawtooth_fourierExpansion` and the
plus sign in `psiH`; the paper prints `ψ = ∑ ψ_H`, cf. the `ed.` notes of §3 in
the tex. -/
def iwaniecMozzochi_section3_psiDecomposition : Prop :=
  ∀ χ : ℝ → ℝ, IsDyadicPartition χ →
    ∃ C : ℝ, ∀ t y : ℝ, 1 ≤ y →
      |sawtooth t + psiH χ (1 / 2 : ℝ) t +
          ∑ j ∈ Finset.range ⌈Real.logb 2 y⌉₊, psiH χ ((2 : ℝ) ^ j) t| ≤
        C * (1 + nearestIntDist t * y)⁻¹

/-- `Δ(x, H, M) = ∑_{m ∼ M} ψ_H(x/m)`. -/
noncomputable def deltaHM (χ : ℝ → ℝ) (x H M : ℝ) : ℝ :=
  ∑ m ∈ dyadic M, psiH χ H (x / m)

/-- `E(x, y, M) = ∑_{m ∼ M} (1 + ‖x/m‖ y)⁻¹`. -/
noncomputable def sawtoothErrorSum (x y M : ℝ) : ℝ :=
  ∑ m ∈ dyadic M, (1 + nearestIntDist (x / m) * y)⁻¹

/-- **§3, elementary bound**: `E(x, y, M) ≪ (1 + M y⁻¹) x^ε`. -/
def iwaniecMozzochi_section3_errorSumBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x y M : ℝ, 1 ≤ x → 1 ≤ y → 1 ≤ M → M ≤ x →
    sawtoothErrorSum x y M ≤ C * (1 + M * y⁻¹) * x ^ ε

/-- **(3.2)** for the ranges **(2.2)** and **(3.3)**: `Δ(x, H, M) ≪ x^{θ+ε}`
for `x^θ < M < x^{1/2}` and `H = 2^j` with `1 ≤ H ≤ M x^{-θ}`. -/
def DeltaHMBound (χ : ℝ → ℝ) (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (x M : ℝ) (j : ℕ),
    1 ≤ x → x ^ θ < M → M < x ^ ((1 : ℝ) / 2) → (2 : ℝ) ^ j ≤ M * x ^ (-θ) →
    |deltaHM χ x ((2 : ℝ) ^ j) M| ≤ C * x ^ (θ + ε)

/-- The bound required for the separate `H = 1/2` Fourier block omitted by
the `H = 2^j`, `j : ℕ`, range in (3.2).  It is deliberately not folded into
`DeltaHMBound`: that definition continues to express exactly the paper's range
`H = 2^j`, `j : ℕ`, hence `H ≥ 1`. -/
def DeltaHalfHMBound (χ : ℝ → ℝ) (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x M : ℝ,
    1 ≤ x → x ^ θ < M → M < x ^ ((1 : ℝ) / 2) →
    |deltaHM χ x (1 / 2 : ℝ) M| ≤ C * x ^ (θ + ε)

/-- **(3.2)** with `θ = 7/22`. -/
def iwaniecMozzochi_eq32 : Prop :=
  ∀ χ : ℝ → ℝ, IsDyadicPartition χ → DeltaHMBound χ theta0

/-- **§3, reduction**: (3.2) for all `H` in (3.3), together with the separate
`H = 1/2` block forced by the dyadic partition, implies (2.1), for any
`0 < θ < 1/2` (take `y = M x^{-θ}`). -/
def iwaniecMozzochi_reduction_eq32 : Prop :=
  ∀ χ : ℝ → ℝ, IsDyadicPartition χ →
    ∀ θ : ℝ, 0 < θ → θ < 1 / 2 →
      DeltaHMBound χ θ → DeltaHalfHMBound χ θ → DeltaMBound θ

/-! ### §4: the van der Corput method -/

/-- **§4, exponent-pair bounds**: with the exponent pairs `(1/2, 1/2)` and
`(2/7, 4/7)`, for `M² ≤ x h`,
`∑_{m ∼ M} e(xh/m) ≪ (xh)^{1/2} M^{-1/2}` and `≪ (xh)^{2/7}`. -/
def iwaniecMozzochi_section4_exponentPairBounds : Prop :=
  ∃ C : ℝ, ∀ x h M : ℝ, 1 ≤ M → M ^ 2 ≤ x * h →
    ‖∑ m ∈ dyadic M, e (x * h / m)‖ ≤ C * ((x * h) ^ ((1 : ℝ) / 2) * M ^ (-(1 : ℝ) / 2)) ∧
    ‖∑ m ∈ dyadic M, e (x * h / m)‖ ≤ C * (x * h) ^ ((2 : ℝ) / 7)

/-- **§4, reduction to (4.1)/(4.2)**: the same bounds hold for `Δ(x, H, M)`,
so (3.2) holds unless `M x^{2θ-1} < H` and `x^{7θ/2 - 1} < H`. -/
def iwaniecMozzochi_section4_reduction : Prop :=
  ∀ χ : ℝ → ℝ, IsDyadicPartition χ → ∀ θ : ℝ, 0 < θ → θ < 1 / 2 →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (x M : ℝ) (j : ℕ),
      1 ≤ x → x ^ θ < M → M < x ^ ((1 : ℝ) / 2) → (2 : ℝ) ^ j ≤ M * x ^ (-θ) →
      ((2 : ℝ) ^ j ≤ M * x ^ (2 * θ - 1) ∨ (2 : ℝ) ^ j ≤ x ^ ((7 : ℝ) / 2 * θ - 1)) →
      |deltaHM χ x ((2 : ℝ) ^ j) M| ≤ C * x ^ (θ + ε)

/-- The main range of §4–§13 with `θ = 7/22`: (2.2), (3.3), (4.1), (4.2). -/
def InMainRange (x H M : ℝ) : Prop :=
  1 ≤ x ∧ x ^ theta0 < M ∧ M < x ^ ((1 : ℝ) / 2) ∧
    1 ≤ H ∧ H ≤ M * x ^ (-theta0) ∧
    M * x ^ (2 * theta0 - 1) < H ∧ x ^ ((7 : ℝ) / 2 * theta0 - 1) < H ∧
    x ^ ((9 : ℝ) / 2 * theta0 - 1) < M

/-! ### §5: Weyl's shift -/

/-- A smooth non-negative weight supported in `[u, v]`. -/
def IsSmoothWeight (φ : ℝ → ℝ) (u v : ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ (∀ t : ℝ, 0 ≤ φ t) ∧
    ∀ t : ℝ, φ t ≠ 0 → u ≤ t ∧ t ≤ v

/-- `T = ∑_n g(n)` with `g(n) = φ(n/N)`. -/
noncomputable def shiftTotal (φ : ℝ → ℝ) (N : ℝ) : ℝ := ∑ᶠ n : ℕ, φ (n / N)

/-- `F = f * g`, `F(m) = ∑_n f(m + n) g(n)` with `g(n) = φ(n/N)`. -/
noncomputable def shiftConv (f : ℕ → ℂ) (φ : ℝ → ℝ) (N : ℝ) (m : ℕ) : ℂ :=
  ∑ᶠ n : ℕ, (φ (n / N) : ℂ) * f (m + n)

/-- **§5, Weyl's shift**: for `|f| ≤ 1` and `g(n) = φ(n/N)` with `φ`
non-negative, `≤ 1`, supported in `[5, 7]`,
`S T = ∑_{m ∼ M} F(m) + O(N²)`. -/
def iwaniecMozzochi_weylShift : Prop :=
  ∃ C : ℝ, ∀ (M N : ℝ) (f : ℕ → ℂ) (φ : ℝ → ℝ), 1 ≤ N → (∀ n : ℕ, ‖f n‖ ≤ 1) →
    (∀ t : ℝ, 0 ≤ φ t ∧ φ t ≤ 1) → (∀ t : ℝ, φ t ≠ 0 → 5 ≤ t ∧ t ≤ 7) →
    ‖(∑ m ∈ dyadic M, f m) * (shiftTotal φ N : ℂ) - ∑ m ∈ dyadic M, shiftConv f φ N m‖ ≤
      C * N ^ 2

/-! ### §6: the special case `f(m) = ψ_H(x/m)` -/

/-- **(6.1)/(6.2)**: `a/c ∈ 𝓡`, i.e. `1 ≤ c ≤ H`, `(a, c) = 1`, and
`c x (2M)⁻² ≤ a ≤ c x M⁻²`. -/
def InFareySet (x H M : ℝ) (a c : ℕ) : Prop :=
  1 ≤ c ∧ (c : ℝ) ≤ H ∧ Nat.Coprime a c ∧
    c * x / (2 * M) ^ 2 ≤ a ∧ (a : ℝ) ≤ c * x / M ^ 2

/-- `m(a/c) = ⌊(c x / a)^{1/2}⌋`. -/
noncomputable def fareyPoint (x : ℝ) (a c : ℕ) : ℕ := ⌊Real.sqrt (c * x / a)⌋₊

/-- `v = (c x / a)^{1/2} - m(a/c) ∈ [0, 1)`. -/
noncomputable def fareyFrac (x : ℝ) (a c : ℕ) : ℝ :=
  Real.sqrt (c * x / a) - fareyPoint x a c

/-- The scale `λ_{a/c} ≍ M³/(x c H)` of (6.3), used as the representative
length of the interval `𝓜_{a/c}`. -/
noncomputable def fareyLength (x H M : ℝ) (c : ℕ) : ℝ := M ^ 3 / (x * c * H)

/-- **(6.3)**, second part: `λ_{a/c} ≫ x^{3/44}` on the main range. -/
def iwaniecMozzochi_eq63 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (x H M : ℝ) (a c : ℕ), InMainRange x H M → InFareySet x H M a c →
    c₀ * x ^ ((3 : ℝ) / 44) ≤ fareyLength x H M c

/-- **(6.4)**: `N = M x^{-2(1-θ)/5}`. -/
noncomputable def shiftLength (x M : ℝ) : ℝ := M * x ^ (-(2 : ℝ) / 5 * (1 - theta0))

/-- **(6.5)**: `G = M³/(x N H)`. -/
noncomputable def Gscale (x H M : ℝ) : ℝ := M ^ 3 / (x * shiftLength x M * H)

/-- **(6.6)**: `1 ≤ G ≤ H` on the main range. -/
def iwaniecMozzochi_eq66 : Prop :=
  ∀ x H M : ℝ, InMainRange x H M → 1 ≤ Gscale x H M ∧ Gscale x H M ≤ H

/-- **(6.12)**: `A = x C M⁻²`. -/
noncomputable def Ascale (x C M : ℝ) : ℝ := x * C / M ^ 2

/-- `F(m) = ∑_n σ(n/N) ψ_H(x/(m+n))`, the convolution of §5 specialised to
`f(m) = ψ_H(x/m)` and `g(n) = σ(n/N)` (§6, §8). -/
noncomputable def convF (χ σ : ℝ → ℝ) (x H N : ℝ) (m : ℕ) : ℝ :=
  ∑ᶠ n : ℕ, σ (n / N) * psiH χ H (x / (m + n))

/-- **(6.11)**: `Δ(x, C, H, M) = (G/C) ∑_{C ≤ c < 2C} ∑_{A/4 < a < 2A, (a, c) = 1} |F(m(a/c))|`. -/
noncomputable def deltaCHM (χ σ : ℝ → ℝ) (x C H M : ℝ) : ℝ :=
  Gscale x H M / C *
    ∑ c ∈ Finset.Ico ⌈C⌉₊ ⌈2 * C⌉₊,
      ∑ a ∈ (Finset.Ioo ⌊Ascale x C M / 4⌋₊ ⌈2 * Ascale x C M⌉₊).filter
          (fun a => Nat.Coprime a c),
        |convF χ σ x H (shiftLength x M) (fareyPoint x a c)|

open Classical in
/-- **(6.9) with (7.6)**: for the convolution weight `φ = ρ * η` of §5 with
`ρ` supported in `[4, 5]`, there are absolute `μ₁ > 0`, `C` such that for
every `x, H, M` in the main range there is `s ∈ [0, 3]` with
`Δ(x, H, M) ≪ x^θ + ∑_{C = 2^j, μ₁ G < C ≤ H} Δ(x, C, H, M) + N`, where
`Δ(x, C, H, M)` is formed with `σ = σ_s = ρ(· - s)`; the term `x^θ` is the
bound (7.6) for the long-interval contribution `Δ₀(x, H, M)`. -/
def iwaniecMozzochi_eq69_eq76 : Prop :=
  ∀ χ ρ : ℝ → ℝ, IsDyadicPartition χ → IsSmoothWeight ρ 4 5 →
    ∃ μ₁ C : ℝ, 0 < μ₁ ∧ ∀ x H M : ℝ, InMainRange x H M →
      ∃ s : ℝ, 0 ≤ s ∧ s ≤ 3 ∧
        |deltaHM χ x H M| ≤
          C * (x ^ theta0 +
            ∑ j ∈ (Finset.range (⌊Real.logb 2 H⌋₊ + 1)).filter
                (fun j => μ₁ * Gscale x H M < (2 : ℝ) ^ j),
              deltaCHM χ (fun t => ρ (t - s)) x ((2 : ℝ) ^ j) H M +
            shiftLength x M)

/-! ### §7: estimate of `S(n, r)` -/

/-- **(7.1)**: `r(l) = -v(2m+v) x h l / (m² (m+v)²) + x h l² / (m² (m+l))`. -/
noncomputable def rPhase (x h m v l : ℝ) : ℝ :=
  -(v * (2 * m + v) * x * h * l) / (m ^ 2 * (m + v) ^ 2) + x * h * l ^ 2 / (m ^ 2 * (m + l))

/-- The trapezoid weight `ω(l) = max{0, 1 + min{l - L₁, L₂ - l, 0}}`. -/
noncomputable def trapezoid (L₁ L₂ l : ℝ) : ℝ := max 0 (1 + min (l - L₁) (min (L₂ - l) 0))

/-- The Fourier integral `∫ ω(l) e(r(l) + k l / c) dl` of (7.2)/(7.3). -/
noncomputable def trapezoidIntegral (x h m v L₁ L₂ c : ℝ) (k : ℤ) : ℂ :=
  ∫ l : ℝ, (trapezoid L₁ L₂ l : ℂ) * e (rPhase x h m v l + k * l / c)

/-- **(7.2)** (Poisson summation): for integers `L₁ < L₂` with `-m < L₁ - 1`,
`∑_l ω(l) e(-a h l / c + r(l)) = ∑_{k ≡ -a h (mod c)} ∫ ω(l) e(r(l) + k l / c) dl`. -/
def iwaniecMozzochi_eq72 : Prop :=
  ∀ (x m v : ℝ) (a c h : ℕ) (L₁ L₂ : ℤ), 0 < x → 0 < h → 0 < m → 0 ≤ v → v < 1 →
    1 ≤ c → L₁ < L₂ → -m < (L₁ : ℝ) - 1 →
    ∑ᶠ l : ℤ, (trapezoid L₁ L₂ l : ℂ) * e (-((a : ℝ) * h * l / c) + rPhase x h m v l) =
      ∑' k : ℤ, if k ≡ -((a : ℤ) * (h : ℤ)) [ZMOD (c : ℤ)] then
        trapezoidIntegral x h m v L₁ L₂ c k else 0

/-- **(7.3)/(7.4)**: in the setting of §6–§7 (`h ∼ H`, `a/c ∈ 𝓡`,
`m = m(a/c)`, `-λ < L₁ < L₂ < 8λ`), there are absolute `k₀, C` with
`∫ ≪ min{c/|k|, c²/k²}` for `|k| ≥ k₀` and `∫ ≪ (x H M⁻³)^{-1/2}` for `|k| < k₀`. -/
def iwaniecMozzochi_eq73_eq74 : Prop :=
  ∃ k₀ C : ℝ, ∀ (x H M : ℝ) (a c h : ℕ) (L₁ L₂ : ℤ),
    InMainRange x H M → InFareySet x H M a c → h ∈ dyadic H → L₁ < L₂ →
    -fareyLength x H M c < L₁ → (L₂ : ℝ) < 8 * fareyLength x H M c →
    (∀ k : ℤ, k₀ ≤ |(k : ℝ)| →
      ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k‖ ≤
        C * min (c / |(k : ℝ)|) ((c : ℝ) ^ 2 / (k : ℝ) ^ 2)) ∧
    (∀ k : ℤ, |(k : ℝ)| < k₀ →
      ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c) L₁ L₂ c k‖ ≤
        C * (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2))

/-- **(7.5)** (the bound (5.6) for `S(n, r)`): for `a/c ∈ 𝓡` with `c ≤ μ₀ G`
(the long intervals `λ_{a/c} ≥ N`, the only case in which (7.5) is used),
`m = m(a/c)` and integers `-λ < L₁ < L₂ < 8λ`,
`∑_{L₁ ≤ l < L₂} ψ_H(x/(m + l)) ≪ c⁻¹ (x H)^{-1/2} M^{3/2}` uniformly in `L₁, L₂`.
(The restriction `c ≤ μ₀ G` is needed for the `log c` of §7 to be absorbed,
and for `c ≍ H` the bound is false; cf. the `ed.` note in §7 of the tex.) -/
def iwaniecMozzochi_eq75 : Prop :=
  ∀ (χ : ℝ → ℝ) (μ₀ : ℝ), IsDyadicPartition χ → 0 < μ₀ →
    ∃ C : ℝ, ∀ (x H M : ℝ) (a c : ℕ) (L₁ L₂ : ℤ),
      InMainRange x H M → InFareySet x H M a c → (c : ℝ) ≤ μ₀ * Gscale x H M → L₁ < L₂ →
      -fareyLength x H M c < L₁ → (L₂ : ℝ) < 8 * fareyLength x H M c →
      |∑ l ∈ Finset.Ico L₁ L₂, psiH χ H (x / (fareyPoint x a c + l))| ≤
        C * ((c : ℝ)⁻¹ * (x * H) ^ (-(1 : ℝ) / 2) * M ^ ((3 : ℝ) / 2))

/-! ### §8: evaluation of `F(m(a/c))` -/

/-- `R(h, m) = ∑_n σ(n/N) e(h x / (m + n))`. -/
noncomputable def Rsum (σ : ℝ → ℝ) (x N : ℝ) (h m : ℕ) : ℂ :=
  ∑ᶠ n : ℕ, (σ (n / N) : ℂ) * e (h * x / (m + n))

/-- The incomplete theta series `θ(α, β) = ∑_n g(n) e(α n + β n²)` of (9.1)
(in §8, `g(n) = σ(n/N)`). -/
noncomputable def incompleteTheta (g : ℝ → ℝ) (α β : ℝ) : ℂ :=
  ∑ᶠ n : ℕ, (g n : ℂ) * e (α * n + β * (n : ℝ) ^ 2)

/-- **(8.1)**: `β = x^{-1/2} (a/c)^{3/2} h`. -/
noncomputable def betaIM (x : ℝ) (a c h : ℕ) : ℝ :=
  x ^ (-(1 : ℝ) / 2) * ((a : ℝ) / c) ^ ((3 : ℝ) / 2) * h

/-- **(8.1)**: `α = -a h / c - 2 v β`. -/
noncomputable def alphaIM (x : ℝ) (a c h : ℕ) : ℝ :=
  -((a : ℝ) * h / c) - 2 * fareyFrac x a c * betaIM x a c h

/-- **(8.2)**: `β N ≪ 1 ≪ β c N` for `a/c ∈ 𝓡` with `c > μ₁ G` (the short
intervals), `h ∼ H`. -/
def iwaniecMozzochi_eq82 : Prop :=
  ∀ μ₁ : ℝ, 0 < μ₁ → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (x H M : ℝ) (a c h : ℕ), InMainRange x H M → InFareySet x H M a c →
      μ₁ * Gscale x H M < c → h ∈ dyadic H →
      betaIM x a c h * shiftLength x M ≤ c₁ ∧
        c₂ ≤ betaIM x a c h * c * shiftLength x M

/-- **(8.4)**: for `σ` smooth and supported in `[4, 8]`, `a/c ∈ 𝓡` with
`c > μ₁ G`, `h ∼ H`, and `m = m(a/c)`,
`R(h, m) = e(x h / m) θ(α, β) + O(x^{1/44})`. -/
def iwaniecMozzochi_eq84 : Prop :=
  ∀ (σ : ℝ → ℝ) (μ₁ : ℝ), IsSmoothWeight σ 4 8 → 0 < μ₁ →
    ∃ C : ℝ, ∀ (x H M : ℝ) (a c h : ℕ), InMainRange x H M → InFareySet x H M a c →
      μ₁ * Gscale x H M < c → h ∈ dyadic H →
      ‖Rsum σ x (shiftLength x M) h (fareyPoint x a c) -
          e (x * h / fareyPoint x a c) *
            incompleteTheta (fun t => σ (t / shiftLength x M))
              (alphaIM x a c h) (betaIM x a c h)‖ ≤
        C * x ^ ((1 : ℝ) / 44)

/-! ### §9: incomplete theta series -/

/-- **(9.6)/(9.7)** (approximate modular relation).  Let `g` be `C³`,
supported in `c₀ N ≤ n ≤ N / c₀`, with `|n^j g^{(j)}(n)| ≤ 1` for
`j = 0, 1, 2, 3` (9.3); let `β > 0`, `α = -(b + η)/c` with `c ≥ 1`,
`-1/2 < η ≤ 1/2` (9.2); assume `β N² ≫ 1`, `β N ≪ 1 ≪ β c N` (9.4) and
`|η| ≪ β c` (9.5).  Then
`θ(α, β) = (i/(2β))^{1/2} ∑_{l ≡ b (mod c)} g(l/(2βc)) e((-l² - 2ηl)/(4βc²)) + R`
with `R ≪ β^{-3/2} N^{-2} min{1, β N ‖b/c‖⁻¹}`. -/
def iwaniecMozzochi_eq96_eq97 : Prop :=
  ∀ c₀ c₁ c₂ c₃ c₄ : ℝ, 0 < c₀ → c₀ < 1 → 0 < c₁ → 0 < c₂ → 0 < c₃ → 0 < c₄ →
    ∃ C : ℝ, ∀ (g : ℝ → ℝ) (N β η : ℝ) (b : ℤ) (c : ℕ),
      ContDiff ℝ 3 g → (∀ t : ℝ, g t ≠ 0 → c₀ * N ≤ t ∧ t ≤ N / c₀) →
      (∀ j : ℕ, j ≤ 3 → ∀ t : ℝ, |t ^ j * iteratedDeriv j g t| ≤ 1) →
      0 < N → 0 < β → 1 ≤ c → -1 / 2 < η → η ≤ 1 / 2 →
      c₁ ≤ β * N ^ 2 → β * N ≤ c₂ → c₃ ≤ β * c * N → |η| ≤ c₄ * β * c →
      ‖incompleteTheta g (-((b + η) / c)) β -
          (Complex.I / (2 * β)) ^ ((1 : ℂ) / 2) *
            ∑ᶠ (l : ℤ) (_ : l ≡ b [ZMOD (c : ℤ)]),
              (g (l / (2 * β * c)) : ℂ) * e ((-(l : ℝ) ^ 2 - 2 * η * l) / (4 * β * c ^ 2))‖ ≤
        C * (β ^ (-(3 : ℝ) / 2) * N ^ (-(2 : ℝ)) *
          minInv 1 (nearestIntDist ((b : ℝ) / c) / (β * N)))

/-! ### §10: evaluation of `F(m(a/c))`, continued -/

/-- **(10.1)**: `γ = x^{-1/2} (a/c)^{3/2}`, so `β = γ h`. -/
noncomputable def gammaIM (x : ℝ) (a c : ℕ) : ℝ :=
  x ^ (-(1 : ℝ) / 2) * ((a : ℝ) / c) ^ ((3 : ℝ) / 2)

/-- `ā`: the inverse of `a` modulo `c`, as a natural number `< c`. -/
noncomputable def modInv (a c : ℕ) : ℕ := ((a : ZMod c)⁻¹).val

/-- `b = ⌊c x / m⌋` of §10 (`m = m(a/c)`). -/
noncomputable def bIM (x : ℝ) (a c : ℕ) : ℕ := ⌊c * x / fareyPoint x a c⌋₊

/-- `κ = c x / m - ⌊c x / m⌋ ∈ [0, 1)` of §10. -/
noncomputable def kappaIM (x : ℝ) (a c : ℕ) : ℝ := Int.fract (c * x / fareyPoint x a c)

/-- The Fourier integral of (10.2),
`I(k, l) = ∫₀^∞ ξ^{-3/2} χ(ξ/H) σ(l/(2γcNξ)) e(-l²/(4γc²ξ) - ξk/c) dξ`
(here `k` is real, since (10.2) uses `I(k - κ, l)`). -/
noncomputable def fourierI (χ σ : ℝ → ℝ) (γ c H N k l : ℝ) : ℂ :=
  ∫ ξ in Set.Ioi (0 : ℝ),
    ((ξ ^ (-(3 : ℝ) / 2) * χ (ξ / H) * σ (l / (2 * γ * c * N * ξ)) : ℝ) : ℂ) *
      e (-(l ^ 2) / (4 * γ * c ^ 2 * ξ) - ξ * k / c)

/-- **(10.2)**: for `a/c ∈ 𝓡` with `c > μ₁ G` and `m = m(a/c)`,
`F(m) = ℑ (-2iγ)^{-1/2} (πc)⁻¹ ∑_l ∑_k e((ā(k + b) - v) l / c) I(k - κ, l) + O(x^{1/44})`. -/
def iwaniecMozzochi_eq102 : Prop :=
  ∀ (χ σ : ℝ → ℝ) (μ₁ : ℝ), IsDyadicPartition χ → IsSmoothWeight σ 4 8 → 0 < μ₁ →
    ∃ C : ℝ, ∀ (x H M : ℝ) (a c : ℕ), InMainRange x H M → InFareySet x H M a c →
      μ₁ * Gscale x H M < c →
      |convF χ σ x H (shiftLength x M) (fareyPoint x a c) -
          ((-2 * Complex.I * (gammaIM x a c : ℂ)) ^ (-(1 : ℂ) / 2) / ((π * c : ℝ) : ℂ) *
            ∑ᶠ l : ℤ, ∑' k : ℤ,
              e (((modInv a c : ℝ) * (k + bIM x a c) - fareyFrac x a c) * l / c) *
                fourierI χ σ (gammaIM x a c) c H (shiftLength x M)
                  (k - kappaIM x a c) l).im| ≤
        C * x ^ ((1 : ℝ) / 44)

/-- **(10.3)**: `L = x C H N M⁻³`. -/
noncomputable def Lscale (x C H M : ℝ) : ℝ := x * C * H * shiftLength x M / M ^ 3

/-- **(10.5)**: `K = x C N² M⁻³`. -/
noncomputable def Kscale (x C M : ℝ) : ℝ := x * C * shiftLength x M ^ 2 / M ^ 3

/-- **(10.4)** and **(10.7)**: `1 ≪ L ≪ C` and `x^{1/22} L ≪ K ≪ x^{1/11} L`
for `μ₁ G < C ≤ H` on the main range. -/
def iwaniecMozzochi_eq104_eq107 : Prop :=
  ∀ μ₁ : ℝ, 0 < μ₁ → ∃ c₁ c₂ c₃ c₄ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧
    ∀ x C H M : ℝ, InMainRange x H M → μ₁ * Gscale x H M < C → C ≤ H →
      c₁ ≤ Lscale x C H M ∧ Lscale x C H M ≤ c₂ * C ∧
      c₃ * x ^ ((1 : ℝ) / 22) * Lscale x C H M ≤ Kscale x C M ∧
      Kscale x C M ≤ c₄ * x ^ ((1 : ℝ) / 11) * Lscale x C H M

/-- **(10.6)**: for `k` outside `μ₂ K < k < μ₃ K` and `l ≍ L`, integrating by
parts `j` times,
`I(k, l) ≪_j (x H N² M⁻³ + |k| H / C)^{-j} ≪ (x^{1/11} + |k|)^{-j}`. -/
def iwaniecMozzochi_eq106 : Prop :=
  ∀ (χ σ : ℝ → ℝ) (μ₁ : ℝ), IsDyadicPartition χ → IsSmoothWeight σ 4 8 → 0 < μ₁ →
    ∃ μ₂ μ₃ : ℝ, 0 < μ₂ ∧ μ₂ < μ₃ ∧ ∀ j : ℕ, ∃ C₀ : ℝ,
      ∀ (x C H M : ℝ) (a c : ℕ) (k : ℝ) (l : ℤ),
        InMainRange x H M → InFareySet x H M a c → μ₁ * Gscale x H M < C → C ≤ H →
        c ∈ Finset.Ico ⌈C⌉₊ ⌈2 * C⌉₊ → l ∈ Finset.Icc ⌈Lscale x C H M⌉ ⌊2 * Lscale x C H M⌋ →
        (k < μ₂ * Kscale x C M ∨ μ₃ * Kscale x C M < k) →
        ‖fourierI χ σ (gammaIM x a c) c H (shiftLength x M) k l‖ ≤
          C₀ * (x * H * shiftLength x M ^ 2 / M ^ 3 + |k| * H / C) ^ (-(j : ℝ)) ∧
        ‖fourierI χ σ (gammaIM x a c) c H (shiftLength x M) k l‖ ≤
          C₀ * (x ^ ((1 : ℝ) / 11) + |k|) ^ (-(j : ℝ))

/-! ### §11: an incomplete Bessel function -/

/-- **(11.1)**: `I_f(a, b) = ∫₀^∞ x^{-3/2} f(x) e(-a x⁻¹ - b x) dx`. -/
noncomputable def incompleteBessel (f : ℝ → ℝ) (a b : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), ((t ^ (-(3 : ℝ) / 2) * f t : ℝ) : ℂ) * e (-a / t - b * t)

/-- The `L²` norm `‖g‖ = (∫ |g(x)|² dx)^{1/2}`. -/
noncomputable def imL2Norm (g : ℝ → ℝ) : ℝ := Real.sqrt (∫ t : ℝ, g t ^ 2)

/-- `∫ y² |f̂(y)| dy`. -/
noncomputable def secondMomentFourier (f : ℝ → ℝ) : ℝ :=
  ∫ y : ℝ, y ^ 2 * ‖𝓕 (fun t : ℝ => (f t : ℂ)) y‖

/-- A smooth function compactly supported in `(0, ∞)`. -/
def IsSmoothCompactPos (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧ ∀ t : ℝ, f t ≠ 0 → 0 < t

/-- **Lemma 11.1, (11.2)/(11.3)**: for `a, b > 0` and `f` smooth, compactly
supported in `(0, ∞)`,
`I_f(a, b) = (2ia)^{-1/2} e(-2√(ab)) f(√(a/b)) + R_f(a, b)` with
`R_f(a, b) ≪ (b^{-3/2} + a^{-1/2} b^{-2}) ∫ y² |f̂(y)| dy`. -/
def iwaniecMozzochi_lemma111_eq112_eq113 : Prop :=
  ∃ C : ℝ, ∀ (f : ℝ → ℝ) (a b : ℝ), IsSmoothCompactPos f → 0 < a → 0 < b →
    ‖incompleteBessel f a b -
        (2 * Complex.I * (a : ℂ)) ^ (-(1 : ℂ) / 2) * e (-2 * Real.sqrt (a * b)) *
          (f (Real.sqrt (a / b)) : ℂ)‖ ≤
      C * ((b ^ (-(3 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) * b ^ (-(2 : ℝ))) * secondMomentFourier f)

/-- **Lemma 11.1, (11.4)**: `∫ y² |f̂(y)| dy ≤ √(2π) ‖f''‖^{1/2} ‖f'''‖^{1/2}`.
(With Mathlib's normalisation of `𝓕` the optimal constant is `(2π)^{-2}`;
the printed constant `√(2π)` is stated, and holds a fortiori.) -/
def iwaniecMozzochi_lemma111_eq114 : Prop :=
  ∀ f : ℝ → ℝ, IsSmoothCompactPos f →
    secondMomentFourier f ≤
      Real.sqrt (2 * π) * imL2Norm (iteratedDeriv 2 f) ^ ((1 : ℝ) / 2) *
        imL2Norm (iteratedDeriv 3 f) ^ ((1 : ℝ) / 2)

/-- **(11.5)**: for `a, b > 0`,
`∫₀^∞ x^{-3/2} e(-a x⁻¹ - b x) dx = (2ia)^{-1/2} e(-2√(ab))`, the integral
being conditionally convergent at `0` and taken as `lim_{δ → 0⁺} ∫_δ^∞`. -/
def iwaniecMozzochi_eq115 : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b →
    Filter.Tendsto
      (fun δ : ℝ => ∫ t in Set.Ioi δ, ((t ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * e (-a / t - b * t))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((2 * Complex.I * (a : ℂ)) ^ (-(1 : ℂ) / 2) * e (-2 * Real.sqrt (a * b))))

/-- **(11.7)**: if `f` vanishes unless `c₀ X ≤ x ≤ X / c₀` and (11.6)
`f'' ≪ X⁻²`, `f''' ≪ X⁻³`, then `R_f(a, b) ≪ (b^{-3/2} + a^{-1/2} b^{-2}) X⁻²`. -/
def iwaniecMozzochi_eq117 : Prop :=
  ∀ c₀ c₁ : ℝ, 0 < c₀ → c₀ < 1 → 0 < c₁ →
    ∃ C : ℝ, ∀ (f : ℝ → ℝ) (a b X : ℝ), IsSmoothCompactPos f → 0 < a → 0 < b → 0 < X →
      (∀ t : ℝ, f t ≠ 0 → c₀ * X ≤ t ∧ t ≤ X / c₀) →
      (∀ t : ℝ, |iteratedDeriv 2 f t| ≤ c₁ * X ^ (-(2 : ℝ))) →
      (∀ t : ℝ, |iteratedDeriv 3 f t| ≤ c₁ * X ^ (-(3 : ℝ))) →
      ‖incompleteBessel f a b -
          (2 * Complex.I * (a : ℂ)) ^ (-(1 : ℂ) / 2) * e (-2 * Real.sqrt (a * b)) *
            (f (Real.sqrt (a / b)) : ℂ)‖ ≤
        C * ((b ^ (-(3 : ℝ) / 2) + a ^ (-(1 : ℝ) / 2) * b ^ (-(2 : ℝ))) * X ^ (-(2 : ℝ)))

/-! ### §12: evaluation of `F(m(a/c))`, completion -/

/-- **(12.2)**: the coefficients `x₁ = (ā b - v)/c`, `x₂ = ā/c`,
`x₃ = -x^{1/4} (ac)^{-3/4}`, `x₄ = (κ/2) x^{1/4} (ac)^{-3/4}`. -/
noncomputable def xCoeff (x : ℝ) (a c : ℕ) : Fin 4 → ℝ :=
  ![((modInv a c : ℝ) * bIM x a c - fareyFrac x a c) / c,
    (modInv a c : ℝ) / c,
    -(x ^ ((1 : ℝ) / 4) * ((a : ℝ) * c) ^ (-(3 : ℝ) / 4)),
    kappaIM x a c / 2 * x ^ ((1 : ℝ) / 4) * ((a : ℝ) * c) ^ (-(3 : ℝ) / 4)]

/-- The bilinear form of (12.3),
`𝓑_{t₁t₂}(𝐱; K, L) = ∑_{k ≍ K} ∑_{l ≍ L} k^{i(t₂-t₁)/2} l^{it₁-1} e(x₁ l + x₂ k l + x₃ k^{1/2} l + x₄ k^{-1/2} l)`. -/
noncomputable def imBilinearForm (x₁ x₂ x₃ x₄ t₁ t₂ K L : ℝ) : ℂ :=
  ∑ k ∈ dyadic K, ∑ l ∈ dyadic L,
    (k : ℂ) ^ (Complex.I / 2 * ((t₂ - t₁ : ℝ) : ℂ)) * (l : ℂ) ^ (Complex.I * (t₁ : ℂ) - 1) *
      e (x₁ * l + x₂ * k * l + x₃ * Real.sqrt k * l + x₄ * l / Real.sqrt k)

open Classical in
/-- `𝓑(A, C, K, L) = (G/C) ∑_{C ≤ c < 2C} ∑_{A/4 < a < 2A, (a, c) = 1} |𝓑_{t₁t₂}(𝐱(a, c); K, L)|`
of (12.4), with the summation ranges of (6.11) (the paper prints `a ∼ A`,
`c ∼ C`, which would omit `A/4 < a ≤ A`; cf. the `ed.` note in §12 of the tex). -/
noncomputable def bigB (x G A C K L t₁ t₂ : ℝ) : ℝ :=
  G / C * ∑ a ∈ Finset.Ioo ⌊A / 4⌋₊ ⌈2 * A⌉₊,
    ∑ c ∈ (Finset.Ico ⌈C⌉₊ ⌈2 * C⌉₊).filter (fun c => Nat.Coprime a c),
    ‖imBilinearForm (xCoeff x a c 0) (xCoeff x a c 1) (xCoeff x a c 2) (xCoeff x a c 3)
      t₁ t₂ K L‖

/-- **(12.4)** with **(12.5)**: for `μ₁ G < C ≤ H` there are `t₁, t₂ ∈ ℝ` with
`Δ(x, C, H, M) ≪ 𝓑(A, C, K, L) + G H M⁻² x^{45/44}`, and
`G H M⁻² x^{45/44} ≍ x^{13/44}`. -/
def iwaniecMozzochi_eq124_eq125 : Prop :=
  ∀ (χ σ : ℝ → ℝ) (μ₁ : ℝ), IsDyadicPartition χ → IsSmoothWeight σ 4 8 → 0 < μ₁ →
    ∃ C₀ : ℝ, ∀ x C H M : ℝ, InMainRange x H M → μ₁ * Gscale x H M < C → C ≤ H →
      (∃ t₁ t₂ : ℝ, deltaCHM χ σ x C H M ≤
        C₀ * (bigB x (Gscale x H M) (Ascale x C M) C (Kscale x C M) (Lscale x C H M) t₁ t₂ +
          Gscale x H M * H * M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44))) ∧
      Gscale x H M * H * M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44) ≤ C₀ * x ^ ((13 : ℝ) / 44) ∧
      x ^ ((13 : ℝ) / 44) ≤ C₀ * (Gscale x H M * H * M ^ (-(2 : ℝ)) * x ^ ((45 : ℝ) / 44))

/-! ### §13: estimation of `𝓑(A, C, K, L)` -/

open Classical in
/-- `𝒩(Δ₁, Δ₂; A, C)`: the number of pairs `(a, c), (a₁, c₁)` with
`a, a₁ ∼ A`, `c, c₁ ∼ C`, `(a, c) = (a₁, c₁) = 1`, satisfying (13.10)
`‖ā/c - ā₁/c₁‖ ≤ Δ₁` and (13.11) `|a c - a₁ c₁| < Δ₂ A C`. -/
noncomputable def fareyPairCount (Δ₁ Δ₂ A C : ℝ) : ℕ :=
  (((dyadic A ×ˢ dyadic C) ×ˢ (dyadic A ×ˢ dyadic C)).filter
    fun q : (ℕ × ℕ) × (ℕ × ℕ) =>
      Nat.Coprime q.1.1 q.1.2 ∧ Nat.Coprime q.2.1 q.2.2 ∧
        nearestIntDist ((modInv q.1.1 q.1.2 : ℝ) / q.1.2 - (modInv q.2.1 q.2.2 : ℝ) / q.2.2) ≤ Δ₁ ∧
        |((q.1.1 * q.1.2 : ℕ) : ℝ) - ((q.2.1 * q.2.2 : ℕ) : ℝ)| < Δ₂ * A * C).card

/-- **Theorem 4.1 of Bombieri–Iwaniec** (as quoted in §13): if `C ≪ A` and
`Δ₁ C² ≫ 1`, then
`𝒩(Δ₁, Δ₂; A, C) ≪ (1 + Δ₁ Δ₂ A C + Δ₁² A C)(A C)^{1+ε}`. -/
def bombieriIwaniec_theorem41 : Prop :=
  ∀ c₀ c₁ ε : ℝ, 0 < c₀ → 0 < c₁ → 0 < ε →
    ∃ C₀ : ℝ, ∀ Δ₁ Δ₂ A C : ℝ, 1 ≤ A → 1 ≤ C → 0 < Δ₁ → 0 < Δ₂ →
      C ≤ c₀ * A → c₁ ≤ Δ₁ * C ^ 2 →
      (fareyPairCount Δ₁ Δ₂ A C : ℝ) ≤
        C₀ * (1 + Δ₁ * Δ₂ * A * C + Δ₁ ^ 2 * A * C) * (A * C) ^ (1 + ε)

/-- **(13.12)**: with `Δ₁ ≍ Y₂⁻¹ = (KL)⁻¹` and `Δ₂ ≍ x^{-1/4} (AC)^{3/4} Y₃⁻¹`,
`𝓑₁ ≤ 𝒩(Δ₁, Δ₂; A, C) ≪ x⁻² C⁻¹ H⁻¹ N⁻⁵ M⁷ (AC)^{1+ε}`. -/
def iwaniecMozzochi_eq1312 : Prop :=
  ∀ μ₁ μ ε : ℝ, 0 < μ₁ → 0 < μ → 0 < ε →
    ∃ C₀ : ℝ, ∀ x C H M : ℝ, InMainRange x H M → μ₁ * Gscale x H M < C → C ≤ H →
      (fareyPairCount (μ / (Kscale x C M * Lscale x C H M))
          (μ * x ^ (-(1 : ℝ) / 4) * (Ascale x C M * C) ^ ((3 : ℝ) / 4) *
            Kscale x C M ^ (-(1 : ℝ) / 2) / Lscale x C H M)
          (Ascale x C M) C : ℝ) ≤
        C₀ * (x ^ (-(2 : ℝ)) * C⁻¹ * H⁻¹ * shiftLength x M ^ (-(5 : ℝ)) * M ^ 7 *
          (Ascale x C M * C) ^ (1 + ε))

open Classical in
/-- `𝓑₂`: the number of 8-tuples `k_j ∼ K`, `l_j ∼ L` satisfying
(13.5) `l₁ + l₂ = l₃ + l₄`, (13.6) `k₁l₁ + k₂l₂ = k₃l₃ + k₄l₄`,
(13.7) `|√k₁ l₁ + √k₂ l₂ - √k₃ l₃ - √k₄ l₄| ≤ μ X₃⁻¹`, and
(13.8) `|l₁/√k₁ + l₂/√k₂ - l₃/√k₃ - l₄/√k₄| ≤ μ X₄⁻¹`. -/
noncomputable def b2Count (μ X₃ X₄ K L : ℝ) : ℕ :=
  (((Fintype.piFinset fun _ : Fin 4 => dyadic K) ×ˢ
      (Fintype.piFinset fun _ : Fin 4 => dyadic L)).filter
    fun q : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
      q.2 0 + q.2 1 = q.2 2 + q.2 3 ∧
      q.1 0 * q.2 0 + q.1 1 * q.2 1 = q.1 2 * q.2 2 + q.1 3 * q.2 3 ∧
      |Real.sqrt (q.1 0) * q.2 0 + Real.sqrt (q.1 1) * q.2 1 -
          Real.sqrt (q.1 2) * q.2 2 - Real.sqrt (q.1 3) * q.2 3| ≤ μ / X₃ ∧
      |(q.2 0 : ℝ) / Real.sqrt (q.1 0) + (q.2 1 : ℝ) / Real.sqrt (q.1 1) -
          (q.2 2 : ℝ) / Real.sqrt (q.1 2) - (q.2 3 : ℝ) / Real.sqrt (q.1 3)| ≤ μ / X₄).card

/-- **(13.13)**: with `X₃ = X₄ = x^{1/4} (AC)^{-3/4}`, `𝓑₂ ≪ (KL)^{2+ε}` (from
Theorem 14.1, ignoring (13.8)). -/
def iwaniecMozzochi_eq1313 : Prop :=
  ∀ μ₁ μ ε : ℝ, 0 < μ₁ → 0 < μ → 0 < ε →
    ∃ C₀ : ℝ, ∀ x C H M : ℝ, InMainRange x H M → μ₁ * Gscale x H M < C → C ≤ H →
      (b2Count μ (x ^ ((1 : ℝ) / 4) * (Ascale x C M * C) ^ (-(3 : ℝ) / 4))
          (x ^ ((1 : ℝ) / 4) * (Ascale x C M * C) ^ (-(3 : ℝ) / 4))
          (Kscale x C M) (Lscale x C H M) : ℝ) ≤
        C₀ * (Kscale x C M * Lscale x C H M) ^ (2 + ε)

/-- **§13, final bound**: `𝓑(A, C, K, L) ≪ x^{7/22 + ε}` (from
`𝓑⁴ ≪ x^{14/11 + ε}`), uniformly in `t₁, t₂`. -/
def iwaniecMozzochi_section13_bigBBound : Prop :=
  ∀ μ₁ ε : ℝ, 0 < μ₁ → 0 < ε →
    ∃ C₀ : ℝ, ∀ x C H M t₁ t₂ : ℝ, InMainRange x H M → μ₁ * Gscale x H M < C → C ≤ H →
      bigB x (Gscale x H M) (Ascale x C M) C (Kscale x C M) (Lscale x C H M) t₁ t₂ ≤
        C₀ * x ^ (theta0 + ε)

/-- **§13, conclusion**: `Δ(x, C, H, M) ≪ x^{7/22 + ε}` for `C, H, M` in
question. -/
def iwaniecMozzochi_section13_deltaCHMBound : Prop :=
  ∀ (χ σ : ℝ → ℝ) (μ₁ ε : ℝ), IsDyadicPartition χ → IsSmoothWeight σ 4 8 → 0 < μ₁ → 0 < ε →
    ∃ C₀ : ℝ, ∀ x C H M : ℝ, InMainRange x H M → μ₁ * Gscale x H M < C → C ≤ H →
      deltaCHM χ σ x C H M ≤ C₀ * x ^ (theta0 + ε)

/-! ### §14: a mean-value theorem -/

/-- The quadruples `(k, l)` counted by (14.1)–(14.3): `l₁ + l₂ = l₃ + l₄`,
`k₁l₁ + k₂l₂ = k₃l₃ + k₄l₄`, `|√k₁ l₁ + √k₂ l₂ - √k₃ l₃ - √k₄ l₄| ≤ δ √K L`. -/
def IsMeanValueSolution (δ K L : ℝ) (q : (Fin 4 → ℕ) × (Fin 4 → ℕ)) : Prop :=
  q.2 0 + q.2 1 = q.2 2 + q.2 3 ∧
  q.1 0 * q.2 0 + q.1 1 * q.2 1 = q.1 2 * q.2 2 + q.1 3 * q.2 3 ∧
  |Real.sqrt (q.1 0) * q.2 0 + Real.sqrt (q.1 1) * q.2 1 -
      Real.sqrt (q.1 2) * q.2 2 - Real.sqrt (q.1 3) * q.2 3| ≤ δ * Real.sqrt K * L

open Classical in
/-- `𝓑(δ, K, L)`: the number of solutions of (14.1)–(14.3) in integers
`1 ≤ k_j ≤ K`, `1 ≤ l_j ≤ L`. -/
noncomputable def meanValueCount (δ K L : ℝ) : ℕ :=
  (((Fintype.piFinset fun _ : Fin 4 => upTo K) ×ˢ
      (Fintype.piFinset fun _ : Fin 4 => upTo L)).filter (IsMeanValueSolution δ K L)).card

/-- The fourth-power integral of (14.4). -/
noncomputable def meanValueIntegral (δ K L : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..1, ∫ β in (0 : ℝ)..1, δ * ∫ γ in (-δ⁻¹)..δ⁻¹,
    ‖∑ k ∈ upTo K, ∑ l ∈ upTo L,
        e (α * l + β * k * l + γ * (Real.sqrt k * l) / (Real.sqrt K * L))‖ ^ 4

/-- **(14.4)**: `𝓑(δ, K, L) ≍ ∫₀¹ ∫₀¹ δ ∫_{-1/δ}^{1/δ} |∑_{k ≤ K} ∑_{l ≤ L} e(αl + βkl + γ √k l/(√K L))|⁴ dγ dβ dα`. -/
def iwaniecMozzochi_eq144 : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ δ K L : ℝ, 0 < δ → δ ≤ 1 → 1 ≤ K → 1 ≤ L →
    c₁ * meanValueIntegral δ K L ≤ meanValueCount δ K L ∧
      (meanValueCount δ K L : ℝ) ≤ c₂ * meanValueIntegral δ K L

/-- **Theorem 14.1**, (14.5): for `δ > 0`, `K, L ≥ 1`, `ε > 0`,
`𝓑(δ, K, L) ≪ (K L³ + K² L² + δ K³ L²)(KL)^ε`. -/
def iwaniecMozzochi_theorem141 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ δ K L : ℝ, 0 < δ → 1 ≤ K → 1 ≤ L →
    (meanValueCount δ K L : ℝ) ≤
      C * (K * L ^ 3 + K ^ 2 * L ^ 2 + δ * K ^ 3 * L ^ 2) * (K * L) ^ ε

/-- The short block `K ≤ k < (1 + η) K` of (14.6)/(14.7). -/
noncomputable def shortBlock (η K : ℝ) : Finset ℕ := Finset.Ico ⌈K⌉₊ ⌈(1 + η) * K⌉₊

open Classical in
/-- `𝓑*(δ, K, L)`: the number of solutions of (14.1)–(14.3) restricted by
(14.6) `K ≤ k_j < (1+η) K` and (14.7) `L ≤ l_j < (1+η) L`. -/
noncomputable def meanValueCountStar (η δ K L : ℝ) : ℕ :=
  (((Fintype.piFinset fun _ : Fin 4 => shortBlock η K) ×ˢ
      (Fintype.piFinset fun _ : Fin 4 => shortBlock η L)).filter
    (IsMeanValueSolution δ K L)).card

/-- **§14, dyadic-type reduction**: for `η > 0` fixed,
`𝓑(δ, K, L) ≪ 𝓑*(δ', K', L') log⁸(2 + K + L)` for some `1 ≤ K' ≤ K`,
`1 ≤ L' ≤ L`, with `δ' = δ √K L / (√K' L')`. -/
def iwaniecMozzochi_section14_reductionToStar : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ δ K L : ℝ, 0 < δ → 1 ≤ K → 1 ≤ L →
    ∃ K' L' : ℝ, 1 ≤ K' ∧ K' ≤ K ∧ 1 ≤ L' ∧ L' ≤ L ∧
      (meanValueCount δ K L : ℝ) ≤
        C * meanValueCountStar η (δ * Real.sqrt K * L / (Real.sqrt K' * L')) K' L' *
          Real.log (2 + K + L) ^ 8

/-- **§14, trivial bounds**: `𝓑*(δ, K, L) ≪ K³ L³` and
`≪ L⁴ K² (1 + δ K) (KL)^ε`.  (The paper prints the second bound without the
factor `(KL)^ε`, which is needed: for `L = 1`, `δ = 1/K` the count is
`≍ K² log K`; cf. the `ed.` note in §14 of the tex.) -/
def iwaniecMozzochi_section14_trivialBounds : Prop :=
  ∀ η ε : ℝ, 0 < η → 0 < ε → ∃ C : ℝ, ∀ δ K L : ℝ, 0 < δ → 1 ≤ K → 1 ≤ L →
    (meanValueCountStar η δ K L : ℝ) ≤ C * K ^ 3 * L ^ 3 ∧
    (meanValueCountStar η δ K L : ℝ) ≤ C * L ^ 4 * K ^ 2 * (1 + δ * K) * (K * L) ^ ε

/-- The normalisation (14.9): `k₁ ≤ k₂`, `k₃ ≤ k₄`, `k₁ ≤ k₃`. -/
def IsOrderedSolution (q : (Fin 4 → ℕ) × (Fin 4 → ℕ)) : Prop :=
  q.1 0 ≤ q.1 1 ∧ q.1 2 ≤ q.1 3 ∧ q.1 0 ≤ q.1 2

open Classical in
/-- `𝓑₁(δ, K, L)` of (14.14): the solutions counted by `𝓑*(δ, K, L)`, with
(14.9), satisfying (14.15) `|(k₃ - k₁)(k₃ - k₂)| < η⁻¹ δ K²`. -/
noncomputable def meanValueCount₁ (η δ K L : ℝ) : ℕ :=
  (((Fintype.piFinset fun _ : Fin 4 => shortBlock η K) ×ˢ
      (Fintype.piFinset fun _ : Fin 4 => shortBlock η L)).filter
    fun q : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
      IsMeanValueSolution δ K L q ∧ IsOrderedSolution q ∧
        |((q.1 2 : ℝ) - q.1 0) * ((q.1 2 : ℝ) - q.1 1)| < η⁻¹ * δ * K ^ 2).card

open Classical in
/-- `𝓑₂(δ, K, L)` of (14.14): the solutions counted by `𝓑*(δ, K, L)`, with
(14.9), satisfying (14.19) `|(k₃ - k₁)(k₃ - k₂)| ≥ η⁻¹ δ K²`. -/
noncomputable def meanValueCount₂ (η δ K L : ℝ) : ℕ :=
  (((Fintype.piFinset fun _ : Fin 4 => shortBlock η K) ×ˢ
      (Fintype.piFinset fun _ : Fin 4 => shortBlock η L)).filter
    fun q : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
      IsMeanValueSolution δ K L q ∧ IsOrderedSolution q ∧
        η⁻¹ * δ * K ^ 2 ≤ |((q.1 2 : ℝ) - q.1 0) * ((q.1 2 : ℝ) - q.1 1)|).card

/-- **(14.18)**: for `η` sufficiently small and `δ` in the range (14.8),
`𝓑₁(δ, K, L) ≪ (K L³ + K² L² + δ K³ L²)(KL)^ε`. -/
def iwaniecMozzochi_eq1418 : Prop :=
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ε : ℝ, 0 < η → η < η₀ → 0 < ε →
    ∃ C : ℝ, ∀ δ K L : ℝ, 1 ≤ K → 1 ≤ L → (K + L) * K ^ (-(2 : ℝ)) < δ → δ < η ^ 3 →
      (meanValueCount₁ η δ K L : ℝ) ≤
        C * (K * L ^ 3 + K ^ 2 * L ^ 2 + δ * K ^ 3 * L ^ 2) * (K * L) ^ ε

/-- **§14, the bound for `𝓑₂`**: for `η` sufficiently small and `δ` in the
range (14.8), `𝓑₂(δ, K, L) ≪ (K² L² + δ K³ L²)(KL)^ε`. -/
def iwaniecMozzochi_section14_B2Bound : Prop :=
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ε : ℝ, 0 < η → η < η₀ → 0 < ε →
    ∃ C : ℝ, ∀ δ K L : ℝ, 1 ≤ K → 1 ≤ L → (K + L) * K ^ (-(2 : ℝ)) < δ → δ < η ^ 3 →
      (meanValueCount₂ η δ K L : ℝ) ≤
        C * (K ^ 2 * L ^ 2 + δ * K ^ 3 * L ^ 2) * (K * L) ^ ε

end LeanProofs.IntegerPoints
