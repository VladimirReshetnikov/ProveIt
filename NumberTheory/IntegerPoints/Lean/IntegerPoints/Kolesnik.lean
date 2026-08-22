import IntegerPoints.ExponentialSums
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Kolesnik, *On the method of exponent pairs*

Formal statements (no proofs) of every numbered result of

> G. Kolesnik, On the method of exponent pairs, Acta Arith. 45 (1985), 115–143,

transcribed in `Papers/On the method of exponent pairs.tex`: the
`n`-dimensional exponent-tuple classes `E_n`, the `Δ`-approximation relation
`f ∼_Δ g` and the function class `𝓕(F; X; Δ)`, Lemma 1 (transformation `B`),
Lemma 2 (transformation `A`), Lemmas A and B, Theorems 1–5, and the numerical
corollaries of the introduction (`139/858`, `139/429`, the conditional
exponent tuples, Rankin's constant).

Every statement is a `Prop`-valued definition; nothing is asserted.

## Encoding of the several-variable analysis

* A function of `n` real variables is `f : (Fin n → ℝ) → ℝ`, and a domain is
  a set `D : Set (Fin n → ℝ)`.  Real `C^∞` means `ContDiff ℝ ∞ f` on all of
  `ℝⁿ` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`), with hypotheses imposed on `D` only;
  every `C^∞` function on a closed box extends to `ℝⁿ`, so nothing is lost.
* `partialDeriv j f` is `∂f/∂x_j`, defined as the one-variable `deriv` of the
  section `t ↦ f (x with x_j := t)`; `mixedDeriv i f` is the multi-index
  derivative `f^{(i)} = ∂^{i₁+⋯+iₙ} f / ∂x₁^{i₁} ⋯ ∂xₙ^{iₙ}`, obtained by
  iterating the partial derivatives coordinate by coordinate (for smooth `f`
  the order is immaterial).  `hessianMinor k f` is `H_k(f)`, the leading
  `k × k` principal minor of the Hessian; `H(f) = H_n(f)`.
* Lattice points are `Fin n → ℤ`; `latticeSum D f = ∑_{x ∈ D ∩ ℤⁿ} e(f(x))` is
  a `finsum` (all domains occurring here are bounded, so the support is
  finite and this is an ordinary finite sum), and `latticeCard D = |D|` is
  the number of lattice points of `D`.
* Kolesnik indexes variables `x₁, …, xₙ`; here they are `x 0, …, x (n-1)`.
  `coord X j` is `X_{j+1}`, `headProduct k X = X₁ ⋯ X_k = N_k`, and
  `tailProduct k X = X_{k+1} ⋯ X_n`.
* The class `𝒟(X)` of admissible domains (§2: subdomains of the dyadic box
  whose boundary consists of at most `C` algebraic curves of degree at most
  `C`) is `IsAlgebraicDomain C X D`: `D` lies in the box and its topological
  frontier is covered by at most `C` real algebraic hypersurfaces of degree at
  most `C`.  The complexity `C` is quantified before the implied constants.
* `f ∼_Δ g` (§2) means `f^{(i)} = g^{(i)} + O(Δ g^{(i)})` on `D` for all
  multi-indices `i`; the implied constant is absorbed into `Δ`
  (`ApproxΔ D Δ f g`).  The monomial `F X₁^{-α₁} ⋯ Xₙ^{-αₙ} x₁^{α₁} ⋯ xₙ^{αₙ}`
  is `monomial F X α`.
* `≪` with a constant depending on parameters `p` is `∀ p, ∃ C, ∀ …, ‖A‖ ≤ C B`;
  `⋘` (`≪ N^ε`) is `∀ ε > 0, ∃ C, …, ‖A‖ ≤ C N^ε B`; `≍` hypotheses carry
  explicit constants `c₁, c₂` quantified before `C`.
* Exponent `(n+1)`-tuples `(λ₀ | λ₁, …, λₙ)` are a pair `lam₀ : ℝ`,
  `lam : Fin n → ℝ`.  `InExponentClass n lam₀ lam` is `λ ∈ E_n`: for every
  admissible `α` and domain complexity, for sufficiently small `Δ`, one has
  `∑_{x ∈ D} e(f(x)) ⋘ F^{λ₀} X₁^{λ₁} ⋯ Xₙ^{λₙ}` for all `f ∈ 𝓕(F; X; Δ)` and
  `D ∈ 𝒟(X)`.  The ordering `X₁ ≥ ⋯ ≥ Xₙ` of §2 is *not* imposed there
  (variables may be relabelled; Theorem 5 appends the `m` new variables
  `h₁, …, h_m` of size `q_j ≤ X_j` after `x₁, …, xₙ`, which would violate the
  ordering), and §2's `X₁ ⋘ F` is imposed as `X_j ≤ F N^ε` for every `j`.
  The same standing condition `X ⋘ F` is imposed explicitly in Theorem 1,
  where it is necessary (see its docstring); Theorem 2 survives without it
  (its `F^{-1/2}` term) and Theorem 3 has the stronger `F ≥ X₁²`.
* Lemma 2 is stated in the `≪ … ∑_h |∑_x …|` form that its Cauchy–Schwarz
  proof gives and that §5 uses, not in the printed `≤ … |∑_{(x,h)} …|` form,
  which is false (see `kolesnik_lemma2`).
* Theorems 4 and 5 are stated in the paper conditionally on the conjectural
  inequalities (1) and (4), which refer to "the best estimate obtainable by
  the method" and are not mathematical statements; here Theorems 4 and 5 are
  stated as unconditional `Prop`s about `E_n`, and the docstrings record the
  caveat.
-/

open scoped BigOperators
open Real Finset

namespace LeanProofs.IntegerPoints

/-! ### Several-variable calculus helpers -/

/-- `∂f/∂x_j`, as the one-variable derivative of the section through `x` in
the `j`-th coordinate direction. -/
noncomputable def partialDeriv {n : ℕ} (j : Fin n) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => deriv (fun t : ℝ => f (Function.update x j t)) (x j)

/-- `∂f/∂x_j` indexed by a natural number; the zero function when `j ≥ n`. -/
noncomputable def partialDerivNat {n : ℕ} (j : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  if h : j < n then partialDeriv ⟨j, h⟩ f else fun _ => 0

/-- The multi-index derivative `f^{(i)} = ∂^{|i|} f / ∂x₁^{i₁} ⋯ ∂xₙ^{iₙ}`,
computed by applying `∂/∂x_j` exactly `i j` times for each `j` (the
coordinates are processed in order; for smooth `f` the order is immaterial). -/
noncomputable def mixedDeriv {n : ℕ} (i : Fin n → ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  Fin.foldr n (fun j g => (partialDeriv j)^[i j] g) f

/-- `H_k(f)(x)`: the determinant of the leading `k × k` principal minor of the
Hessian of `f` at `x` (Kolesnik, §2).  `H(f) = H_n(f)`. -/
noncomputable def hessianMinor {n : ℕ} (k : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  Matrix.det (Matrix.of fun i j : Fin k =>
    partialDerivNat (i : ℕ) (partialDerivNat (j : ℕ) f) x)

/-- Real `C^∞` on `ℝⁿ`. -/
def IsSmooth {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f

/-- `X_{j+1}` read off a size vector, `1` outside the index range. -/
noncomputable def coord {n : ℕ} (X : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then X ⟨j, h⟩ else 1

/-- `N_k = X₁ ⋯ X_k`. -/
noncomputable def headProduct {n : ℕ} (k : ℕ) (X : Fin n → ℝ) : ℝ :=
  ∏ j ∈ Finset.range k, coord X j

/-- `X_{k+1} ⋯ X_n`. -/
noncomputable def tailProduct {n : ℕ} (k : ℕ) (X : Fin n → ℝ) : ℝ :=
  ∏ j ∈ Finset.Ico k n, coord X j

/-- `N = X₁ ⋯ Xₙ`. -/
noncomputable def totalProduct {n : ℕ} (X : Fin n → ℝ) : ℝ := ∏ j, X j

/-! ### Domains, lattice points, exponential sums -/

/-- The dyadic box `{x | X_j ≤ x_j ≤ 2 X_j, j = 1, …, n}`. -/
def dyadicBox {n : ℕ} (X : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ j, X j ≤ x j ∧ x j ≤ 2 * X j}

/-- A domain of the class `𝒟(X)` of Kolesnik, §2, with complexity `C`: a
subset of the dyadic box whose boundary is contained in the union of at most
`C` real algebraic hypersurfaces of degree at most `C`. -/
def IsAlgebraicDomain {n : ℕ} (C : ℕ) (X : Fin n → ℝ) (D : Set (Fin n → ℝ)) : Prop :=
  D ⊆ dyadicBox X ∧
    ∃ P : Fin C → MvPolynomial (Fin n) ℝ,
      (∀ k, P k ≠ 0 ∧ (P k).totalDegree ≤ C) ∧
        frontier D ⊆ ⋃ k, {x | MvPolynomial.eval x (P k) = 0}

/-- The real point of an integer vector. -/
def realVec {n : ℕ} (x : Fin n → ℤ) : Fin n → ℝ := fun j => (x j : ℝ)

/-- The lattice points of `D`. -/
def latticePoints {n : ℕ} (D : Set (Fin n → ℝ)) : Set (Fin n → ℤ) :=
  {x | realVec x ∈ D}

/-- `|D|`: the number of lattice points of `D`. -/
noncomputable def latticeCard {n : ℕ} (D : Set (Fin n → ℝ)) : ℕ :=
  (latticePoints D).ncard

/-- The exponential sum `∑_{x ∈ D} e(f(x))` over the lattice points of `D`. -/
noncomputable def latticeSum {n : ℕ} (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℂ :=
  ∑ᶠ x : Fin n → ℤ, Set.indicator (latticePoints D) (fun y => e (f (realVec y))) x

/-- `D(B₁₁, B₁₂, …, Bₙ₁, Bₙ₂) = {x ∈ D | B_{j1} ≤ x_j ≤ B_{j2}}` (§2). -/
def restrictDomain {n : ℕ} (D : Set (Fin n → ℝ)) (B : Fin n → ℝ × ℝ) : Set (Fin n → ℝ) :=
  {x ∈ D | ∀ j, (B j).1 ≤ x j ∧ x j ≤ (B j).2}

/-- `D(m; f) = {(y₁, …, y_m, x_{m+1}, …, xₙ) | y_j = ∂f/∂x_j (x), x ∈ D}` (§2):
the first `m` coordinates are replaced by the corresponding gradient
components. -/
def gradientImage {n : ℕ} (m : ℕ) (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    Set (Fin n → ℝ) :=
  {z | ∃ x ∈ D, z = fun j : Fin n => if (j : ℕ) < m then partialDeriv j f x else x j}

/-! ### The approximation relation `∼_Δ` and the class `𝓕(F; X; Δ)` -/

/-- `f ∼_Δ g` on `D` (§2): `|f^{(i)} - g^{(i)}| ≤ Δ |g^{(i)}|` on `D` for every
multi-index `i` (the implied constant of `O(Δ g^{(i)})` is absorbed into `Δ`). -/
def ApproxΔ {n : ℕ} (D : Set (Fin n → ℝ)) (Δ : ℝ) (f g : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (i : Fin n → ℕ), ∀ x ∈ D, |mixedDeriv i f x - mixedDeriv i g x| ≤ Δ * |mixedDeriv i g x|

/-- The monomial `F X₁^{-α₁} ⋯ Xₙ^{-αₙ} x₁^{α₁} ⋯ xₙ^{αₙ} = F ∏ (x_j / X_j)^{α_j}`. -/
noncomputable def monomial {n : ℕ} (F : ℝ) (X α : Fin n → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => F * ∏ j, (x j / X j) ^ α j

/-- The exponents `α` are admissible for `𝓕` (§2): no sum
`α_{j₁} + ⋯ + α_{j_i}` over a nonempty set of indices is an integer. -/
def AdmissibleExponents {n : ℕ} (α : Fin n → ℝ) : Prop :=
  ∀ s : Finset (Fin n), s.Nonempty → ∀ k : ℤ, ∑ j ∈ s, α j ≠ k

/-- `f ∈ 𝓕(F; X; Δ)` with exponents `α` on the domain `D` (§2): `f` is real
`C^∞` and `f ∼_Δ F X₁^{-α₁} ⋯ Xₙ^{-αₙ} x₁^{α₁} ⋯ xₙ^{αₙ}` on `D`.  (The side
conditions "`α` admissible" and "`X₁ ⋘ F`" are imposed separately where the
class is used.) -/
def InClassF {n : ℕ} (α : Fin n → ℝ) (F : ℝ) (X : Fin n → ℝ) (Δ : ℝ)
    (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : Prop :=
  IsSmooth f ∧ ApproxΔ D Δ f (monomial F X α)

/-! ### Exponent `(n+1)`-tuples, `E_n` -/

/-- `(λ₀ | λ₁, …, λₙ) ∈ E_n` (Kolesnik, §1): the entries are nonnegative and,
for every admissible exponent vector `α` and every domain complexity `C₀`,
there is a `Δ > 0` such that for every `ε > 0` there is `C` with
`|∑_{x ∈ D} e(f(x))| ≤ C N^ε F^{λ₀} X₁^{λ₁} ⋯ Xₙ^{λₙ}` for all sizes
`X_j ≥ 1`, `F > 0` with `X_j ≤ F N^ε`, all `D ∈ 𝒟(X)` of complexity `C₀` and
all `f ∈ 𝓕(F; X; Δ)`.  See the module docstring for the conventions. -/
def InExponentClass (n : ℕ) (lam₀ : ℝ) (lam : Fin n → ℝ) : Prop :=
  0 ≤ lam₀ ∧ (∀ j, 0 ≤ lam j) ∧
    ∀ (α : Fin n → ℝ), AdmissibleExponents α → ∀ C₀ : ℕ, ∃ Δ : ℝ, 0 < Δ ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
        ∀ (F : ℝ) (X : Fin n → ℝ) (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
          (∀ j, 1 ≤ X j) → 0 < F → (∀ j, X j ≤ F * totalProduct X ^ ε) →
          IsAlgebraicDomain C₀ X D → InClassF α F X Δ D f →
          ‖latticeSum D f‖ ≤ C * totalProduct X ^ ε * F ^ lam₀ * ∏ j, X j ^ lam j

/-- The trivial exponent tuple `(0 | 1, …, 1) ∈ E_n` (§1: "we start with the
e.p. `(0 | 1, …, 1)`"). -/
def kolesnik_trivialTuple : Prop :=
  ∀ n : ℕ, InExponentClass n 0 (fun _ => 1)

/-! ### Transformation `B` (Lemma 1) -/

/-- A real function that does not change sign on `D`. -/
def SignConstantOn {n : ℕ} (D : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ x ∈ D, 0 ≤ g x) ∨ (∀ x ∈ D, g x ≤ 0)

/-- The `c`-tuples `i = (i₁, …, i_c)` of multi-indices `i_l ∈ {0, …, c}ⁿ`. -/
def multiIndexTuples (n c : ℕ) : Finset (Fin c → (Fin n → ℕ)) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Finset.range (c + 1)

/-- Hypothesis (i) of Lemma 1: for all integers `a_i ∈ [-c, c]`, the function
`∑_i a_i ∏_{l ≤ c} f^{(i_l)}(x)` (a polynomial of degree `≤ c` with small
integer coefficients in the derivatives of `f` of orders `≤ c`) does not
change sign on `D`. -/
def DerivativeSignCondition {n : ℕ} (c : ℕ) (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    Prop :=
  ∀ a : (Fin c → (Fin n → ℕ)) → ℤ, (∀ i, |a i| ≤ (c : ℤ)) →
    SignConstantOn D fun x =>
      ∑ i ∈ multiIndexTuples n c, (a i : ℝ) * ∏ l, mixedDeriv (i l) f x

/-- `φ` is a solution map for the system `∂f/∂x_j (φ₁, …, φ_k, x_{k+1}, …, xₙ) = m_j`
(`j = 1, …, k`) of Lemma 1 on `D₁`: for `z = (m, x_{k+1}, …, xₙ) ∈ D₁`, the
point `φ z` lies in `D₃`, agrees with `z` in the last `n - k` coordinates,
and its first `k` gradient components are `m`. -/
def IsStationarySolution {n : ℕ} (k : ℕ) (D₁ D₃ : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ z ∈ D₁, φ z ∈ D₃ ∧ (∀ j : Fin n, k ≤ (j : ℕ) → φ z j = z j) ∧
    ∀ j : Fin n, (j : ℕ) < k → partialDeriv j f (φ z) = z j

/-- The transformed phase
`f₁(m, x_{k+1}, …, xₙ) = f(φ₁, …, φ_k, x_{k+1}, …, xₙ) - φ₁ m₁ - ⋯ - φ_k m_k`
of Lemma 1, for a solution map `φ`. -/
noncomputable def bTransformed {n : ℕ} (k : ℕ) (f : (Fin n → ℝ) → ℝ)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) : (Fin n → ℝ) → ℝ :=
  fun z => f (φ z) - ∑ j : Fin n, if (j : ℕ) < k then φ z j * z j else 0

/-- **Kolesnik, Lemma 1** (transformation `B`).  Let `f` be real `C^∞` on
`D ∈ 𝒟(X)` with (i) the sign condition `DerivativeSignCondition c D f`,
(ii) `|f^{(i)}| ≪_i F X₁^{-i₁} ⋯ Xₙ^{-iₙ}`, and (iii) `|H_k(f)| ≍ A_k⁻¹` for
some `k ∈ [1, n]` and `A_k ≤ (X₁ ⋯ X_k)² F^{1/6 - ε - k}`.  Then there are
reals `B_{ij}` such that, with `D₃ = D(B₁₃, B₁₄, …)`, `D₂ = D₃(k; f)` and
`D₁ = D₂(B₁₁, B₁₂, …)`, for every solution map `φ` of the stationary-phase
system,
`S ≪ √A_k |∑_{(m, x'') ∈ D₁} e(f₁(m, x''))| + N^ε + N^{1+ε} √(F^{k-1} A_k N_k⁻²)`
and
`S ≪ |D| A_k^{-1/2} + N^{1+ε} √(F^{k-1} A_k N_k⁻²) + N^ε + N X_k⁻¹ A_k^{-1/2}
     + X_{k+1} ⋯ Xₙ (F/X₂ + 1) ⋯ (F/X_k + 1) √A_k`.
The implied constants depend on `n, k, c`, the domain complexity `C₀`, `ε`,
the constants `cd i` of (ii) and `c₁, c₂` of (iii). -/
def kolesnik_lemma1 : Prop :=
  ∀ (n k c C₀ : ℕ) (ε c₁ c₂ : ℝ) (cd : (Fin n → ℕ) → ℝ),
    1 ≤ k → k ≤ n → 0 < ε → 0 < c₁ → 0 < c₂ →
    ∃ C : ℝ, ∀ (F A : ℝ) (X : Fin n → ℝ) (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
      (∀ j, 1 ≤ X j) → 0 < F → 0 < A → IsAlgebraicDomain C₀ X D → IsSmooth f →
      DerivativeSignCondition c D f →
      (∀ (i : Fin n → ℕ), ∀ x ∈ D, |mixedDeriv i f x| ≤ cd i * F * ∏ j, X j ^ (-(i j : ℝ))) →
      (∀ x ∈ D, c₁ / A ≤ |hessianMinor k f x| ∧ |hessianMinor k f x| ≤ c₂ / A) →
      A ≤ headProduct k X ^ 2 * F ^ ((1 : ℝ) / 6 - ε - k) →
      ∃ B B' : Fin n → ℝ × ℝ,
        ∀ φ : (Fin n → ℝ) → (Fin n → ℝ),
          IsStationarySolution k (restrictDomain (gradientImage k (restrictDomain D B') f) B)
            (restrictDomain D B') f φ →
          ‖latticeSum D f‖ ≤
            C * (Real.sqrt A *
                  ‖latticeSum (restrictDomain (gradientImage k (restrictDomain D B') f) B)
                    (bTransformed k f φ)‖ +
                totalProduct X ^ ε +
                totalProduct X ^ (1 + ε) *
                  Real.sqrt (F ^ ((k : ℝ) - 1) * A / headProduct k X ^ 2)) ∧
          ‖latticeSum D f‖ ≤
            C * ((latticeCard D : ℝ) / Real.sqrt A +
                totalProduct X ^ (1 + ε) *
                  Real.sqrt (F ^ ((k : ℝ) - 1) * A / headProduct k X ^ 2) +
                totalProduct X ^ ε +
                totalProduct X / coord X (k - 1) / Real.sqrt A +
                tailProduct k X * (∏ j ∈ Finset.Ico 1 k, (F / coord X j + 1)) * Real.sqrt A)

/-! ### Transformation `A` (Lemma 2) -/

/-- `f₁(x, h) = ∫₀¹ ∂/∂t f(x + t h) dt` of Lemma 2. -/
noncomputable def aTransformed {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x h : Fin n → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv (fun s : ℝ => f (x + s • h)) t

/-- The inner sum `∑_{x ∈ D, x + h ∈ D} e(f₁(x, h))` of Lemma 2 for a fixed
integer shift `h`. -/
noncomputable def aShiftedSum {n : ℕ} (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (h : Fin n → ℤ) : ℂ :=
  ∑ᶠ x : Fin n → ℤ,
    Set.indicator {x | realVec x ∈ D ∧ realVec (x + h) ∈ D}
      (fun x' => e (aTransformed f (realVec x') (realVec h))) x

/-- `∑_h |∑_x e(f₁(x, h))|`, the sum over the shifts `h ≠ 0`, `|h_j| ≤ q_j`, of
the moduli of the inner sums over `{x | (x, h) ∈ D₁}` of Lemma 2.  (Only the
first `m` variables are differenced: `q_j = 0` for `j > m` forces `h_j = 0`
there.) -/
noncomputable def aShiftSumAbs {n : ℕ} (D : Set (Fin n → ℝ)) (q : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ᶠ h : Fin n → ℤ,
    Set.indicator {h | h ≠ 0 ∧ ∀ j, |(h j : ℝ)| ≤ q j} (fun h' => ‖aShiftedSum D f h'‖) h

/-- **Kolesnik, Lemma 2** (transformation `A`, Weyl–van der Corput in `m`
variables).  Let `f` be real, `D ∈ 𝒟(X)`, `q₁, …, q_m > 0`
with `q₁/X₁ = ⋯ = q_m/X_m = (Q/N_m)^{1/m}`, `Q = q₁ ⋯ q_m`, `N_m = X₁ ⋯ X_m`
(and `q_j = 0` for `j > m`), and let `|D| ≥ ∑_{x ∈ D} 1` with
`q₁/X₁ ≤ |D|/N`.  Then
`|∑_{x ∈ D} e(f(x))|² ≪ |D|² Q⁻¹ + |D| Q⁻¹ ∑_h |∑_{x : (x, h) ∈ D₁} e(f₁(x, h))|`,
the implied constant depending on `n`, `m` and the domain complexity `C₀`.

The paper prints this with `≤` (constant `1`) and with a single modulus
`|∑_{(x, h) ∈ D₁} e(f₁(x, h))|`; that version is false (already for
`n = m = 1`, `D = [X, 2X]`, `f(x) = θx` and `q³ ≫ X²`; see the `% ed.:` note in
the transcription), and the form stated here is what the Cauchy–Schwarz proof
gives and what the paper uses in §5. -/
def kolesnik_lemma2 : Prop :=
  ∀ (n m C₀ : ℕ), 1 ≤ m → m ≤ n → ∃ C : ℝ,
    ∀ (X q : Fin n → ℝ) (Dcard : ℝ) (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
    (∀ j, 0 < X j) → IsAlgebraicDomain C₀ X D →
    (∀ j : Fin n, (j : ℕ) < m → 0 < q j) → (∀ j : Fin n, m ≤ (j : ℕ) → q j = 0) →
    (∀ j : Fin n, (j : ℕ) < m →
      q j / X j = ((∏ i : Fin n, if (i : ℕ) < m then q i else 1) / headProduct m X) ^ (1 / (m : ℝ))) →
    (latticeCard D : ℝ) ≤ Dcard → coord q 0 / coord X 0 ≤ Dcard / totalProduct X →
    ‖latticeSum D f‖ ^ 2 ≤
      C * (Dcard ^ 2 / (∏ i : Fin n, if (i : ℕ) < m then q i else 1) +
        Dcard / (∏ i : Fin n, if (i : ℕ) < m then q i else 1) * aShiftSumAbs D q f)

/-! ### Lemmas A and B (two variables) -/

/-- **Kolesnik, Lemma A.**  Let `f` be real `C^∞` on `𝒟 ⊆ [X, 2X] × [Y, 2Y]`
such that for all `i, j` and `c` the equation `f_{x^i y^j} = c` has `O(N^ε)`
(lattice-point) solutions in `𝒟`, `|f_{x^i y^j}| ≪_{i,j} F X^{-i} Y^{-j}`,
`|f_{x²}| ≍ M₁⁻¹ ≫ F^{2/3 + ε₀} X⁻²` and `|f_{x²} f_{y²} - f_{xy}²| ≍ M₂⁻¹`,
`N = XY`.  Then
`|∑_{(x,y) ∈ 𝒟} e(f(x,y))| ⋘ |𝒟| M₂^{-1/2} + Y M₁^{1/2} + F M₂^{1/2} / X`. -/
def kolesnik_lemmaA : Prop :=
  ∀ (C₀ : ℕ) (ε ε₀ c₀ c₁ c₂ c₃ c₄ : ℝ) (cd : ℕ → ℕ → ℝ),
    0 < ε → 0 < ε₀ → 0 < c₀ → 0 < c₁ → 0 < c₂ → 0 < c₃ → 0 < c₄ →
    ∃ C : ℝ, ∀ (F X Y M₁ M₂ : ℝ) (D : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → ℝ),
      1 ≤ X → 1 ≤ Y → 0 < F → 0 < M₁ → 0 < M₂ →
      IsAlgebraicDomain C₀ ![X, Y] D → IsSmooth f →
      (∀ (i j : ℕ) (c : ℝ),
        (latticeCard {p ∈ D | mixedDeriv (![i, j] : Fin 2 → ℕ) f p = c} : ℝ) ≤
          c₀ * (X * Y) ^ ε) →
      (∀ (i j : ℕ), ∀ p ∈ D,
        |mixedDeriv (![i, j] : Fin 2 → ℕ) f p| ≤ cd i j * F * X ^ (-(i : ℝ)) * Y ^ (-(j : ℝ))) →
      (∀ p ∈ D, c₁ / M₁ ≤ |mixedDeriv (![2, 0] : Fin 2 → ℕ) f p| ∧
        |mixedDeriv (![2, 0] : Fin 2 → ℕ) f p| ≤ c₂ / M₁) →
      F ^ ((2 : ℝ) / 3 + ε₀) * X ^ (-(2 : ℝ)) ≤ 1 / M₁ →
      (∀ p ∈ D, c₃ / M₂ ≤ |hessianMinor 2 f p| ∧ |hessianMinor 2 f p| ≤ c₄ / M₂) →
      ‖latticeSum D f‖ ≤
        C * (X * Y) ^ ε *
          ((latticeCard D : ℝ) / Real.sqrt M₂ + Y * Real.sqrt M₁ + F * Real.sqrt M₂ / X)

/-- **Kolesnik, Lemma B.**  Let `k ≥ 2`, `K = 2^k`, and let `f` be real `C^∞`
on `𝒟 ⊆ [X, 2X] × [Y, 2Y]` with `|f_{x^k}| ≍ a M⁻¹ X⁻²` and
`|f_{x^{k-2} y²}| ≍ b M⁻¹ Y⁻²`, `N = XY`.  Then
`|∑_{(x,y) ∈ 𝒟} e(f(x,y))| ⋘ min{ |𝒟| (a M⁻¹ X⁻²)^{1/(K-2)} + |𝒟|^{1-2/K} Y^{2/K} (k-2)
    + |𝒟|^{1-2k/K} N^{4/K} (M/a)^{2/K} ;
  |𝒟| (b M⁻¹ Y⁻²)^{1/(K-2)} + |𝒟|^{1-2/K} X^{2/K} (k-2) + |𝒟|^{1-2k/K} N^{4/K} (M/b)^{2/K} }`. -/
def kolesnik_lemmaB : Prop :=
  ∀ (C₀ k : ℕ) (ε c₁ c₂ c₃ c₄ : ℝ),
    2 ≤ k → 0 < ε → 0 < c₁ → 0 < c₂ → 0 < c₃ → 0 < c₄ →
    ∃ C : ℝ, ∀ (X Y M a b : ℝ) (D : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → ℝ),
      1 ≤ X → 1 ≤ Y → 0 < M → 0 < a → 0 < b →
      IsAlgebraicDomain C₀ ![X, Y] D → IsSmooth f →
      (∀ p ∈ D, c₁ * a / (M * X ^ 2) ≤ |mixedDeriv (![k, 0] : Fin 2 → ℕ) f p| ∧
        |mixedDeriv (![k, 0] : Fin 2 → ℕ) f p| ≤ c₂ * a / (M * X ^ 2)) →
      (∀ p ∈ D, c₃ * b / (M * Y ^ 2) ≤ |mixedDeriv (![k - 2, 2] : Fin 2 → ℕ) f p| ∧
        |mixedDeriv (![k - 2, 2] : Fin 2 → ℕ) f p| ≤ c₄ * b / (M * Y ^ 2)) →
      ‖latticeSum D f‖ ≤
        C * (X * Y) ^ ε *
          min ((latticeCard D : ℝ) * (a / (M * X ^ 2)) ^ (1 / (2 ^ k - 2 : ℝ)) +
                (latticeCard D : ℝ) ^ (1 - 2 / 2 ^ k : ℝ) * Y ^ (2 / 2 ^ k : ℝ) * ((k : ℝ) - 2) +
                (latticeCard D : ℝ) ^ (1 - 2 * k / 2 ^ k : ℝ) * (X * Y) ^ (4 / 2 ^ k : ℝ) *
                  (M / a) ^ (2 / 2 ^ k : ℝ))
              ((latticeCard D : ℝ) * (b / (M * Y ^ 2)) ^ (1 / (2 ^ k - 2 : ℝ)) +
                (latticeCard D : ℝ) ^ (1 - 2 / 2 ^ k : ℝ) * X ^ (2 / 2 ^ k : ℝ) * ((k : ℝ) - 2) +
                (latticeCard D : ℝ) ^ (1 - 2 * k / 2 ^ k : ℝ) * (X * Y) ^ (4 / 2 ^ k : ℝ) *
                  (M / b) ^ (2 / 2 ^ k : ℝ))

/-! ### Theorem 1 (double sums) -/

/-- The upper bound for `Q₁` in Theorem 1: the minimum of the two expressions
of (5) (with `K₁ = 2^{k₁}`, `K₂ = 2^{k₂}`) and of the additional bounds
`min{(F² N⁻³)^{11/115}, (N⁵ F⁻²)^{1/13}, (N⁴⁷ F⁻¹⁸)^{1/151}}` for `k₁ = 3`,
`min{(F N⁻¹)^{2/5}, (N² F⁻¹)^{9/29}}` for `k₁ = 2`, and
`min{Δ⁻¹, N^{2/7}}` for `k₁ = 1`.  "`Q₁` is the largest number satisfying
the inequalities" of the theorem, so `Q₁` is this minimum. -/
noncomputable def theorem1Q₁ (k₁ k₂ : ℕ) (N F Δ : ℝ) : ℝ :=
  let K₁ : ℝ := 2 ^ k₁
  let K₂ : ℝ := 2 ^ k₂
  min
    (min
      ((N ^ (2 * k₁ * K₁ + 4 * K₁ - k₁ * k₂ - 2 * k₁ - k₂ - 4 : ℝ) *
          F ^ (2 * k₂ + 4 - 4 * K₁ : ℝ)) ^
        (1 / (4 * K₁ * K₂ - 2 * K₂ - k₂ * K₁ - 3 * K₁ + k₂ + 2) : ℝ))
      ((N ^ (3 * k₁ * K₂ + 6 * K₂ - 2 * k₁ - 2 : ℝ) * F ^ (4 - 6 * K₂ : ℝ)) ^
        (1 / (6 * K₁ * K₂ - 2 * K₁ - 3 * K₂ + 2) : ℝ)))
    (if k₁ = 3 then
      min ((F ^ 2 * N ^ (-(3 : ℝ))) ^ ((11 : ℝ) / 115))
        (min ((N ^ 5 * F ^ (-(2 : ℝ))) ^ ((1 : ℝ) / 13))
          ((N ^ 47 * F ^ (-(18 : ℝ))) ^ ((1 : ℝ) / 151)))
    else if k₁ = 2 then
      min ((F / N) ^ ((2 : ℝ) / 5)) ((N ^ 2 / F) ^ ((9 : ℝ) / 29))
    else
      min Δ⁻¹ (N ^ ((2 : ℝ) / 7)))

/-- The lower bound required of `Q₁` in Theorem 1: `(N Δ²)^{1/4}` for
`k₁ = 3`, `(N Δ²)^{1/2}` for `k₁ = 2`, none (`0`) for `k₁ = 1`. -/
noncomputable def theorem1LowerBound (k₁ : ℕ) (N Δ : ℝ) : ℝ :=
  if k₁ = 3 then (N * Δ ^ 2) ^ ((1 : ℝ) / 4)
  else if k₁ = 2 then (N * Δ ^ 2) ^ ((1 : ℝ) / 2)
  else 0

/-- **Kolesnik, Theorem 1.**  Let `1 ≤ k₁, k₂ ≤ 3`, let `α, β` be non-integers
with `α + β ∉ {k₁, k₁ + 1, k₁ + 1 + 1/k₂}` and `(α - k₁ - 1)² + β (α - k₁) ≠ 0`,
let `Δ` be small, and let `f` be real `C^∞` on `D ⊆ [X, 2X] × [Y, 2Y]` with
`f ∼_Δ F X^{-α} Y^{-β} x^α y^β`, `X ≥ Y`, `XY = N`, and `X ⋘ F` (the
standing condition of the class `𝓕`, §2; without it the theorem is false:
for `F ≤ 1/10` one has `S ≥ |D|/2`, while `Q₁ = N^{2/7}` for `k₁ = 1` and
small `Δ`).  Then
`S = |∑_{(x,y) ∈ D} e(f(x,y))| ⋘ N / √Q₁`, where `Q₁ = theorem1Q₁ k₁ k₂ N F Δ`
is the largest number satisfying (5) and the additional `k₁`-dependent bounds,
and the theorem requires `theorem1LowerBound k₁ N Δ ≤ Q₁`. -/
def kolesnik_theorem1 : Prop :=
  ∀ (k₁ k₂ C₀ : ℕ) (α β : ℝ),
    1 ≤ k₁ → k₁ ≤ 3 → 1 ≤ k₂ → k₂ ≤ 3 →
    (∀ k : ℤ, α ≠ k) → (∀ k : ℤ, β ≠ k) →
    α + β ≠ k₁ → α + β ≠ k₁ + 1 → (α - k₁ - 1) ^ 2 + β * (α - k₁) ≠ 0 →
    α + β ≠ k₁ + 1 + 1 / (k₂ : ℝ) →
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ (F X Y N Δ : ℝ) (D : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → ℝ),
        0 < Δ → Δ ≤ Δ₀ → 0 < F → 1 ≤ Y → Y ≤ X → X * Y = N → X ≤ F * N ^ ε →
        IsAlgebraicDomain C₀ ![X, Y] D → IsSmooth f →
        ApproxΔ D Δ f (monomial F ![X, Y] ![α, β]) →
        theorem1LowerBound k₁ N Δ ≤ theorem1Q₁ k₁ k₂ N F Δ →
        ‖latticeSum D f‖ ≤ C * N ^ ε * (N / Real.sqrt (theorem1Q₁ k₁ k₂ N F Δ))

/-! ### Theorem 2 (triple sums) -/

/-- **Kolesnik, Theorem 2.**  Let `α, β, γ` be reals with
`α + β + γ ∉ {1, 2}` and `αβγ(α-1)(β-1)(γ-1) ≠ 0`, and `Δ ≤ ε₀`.  Let `f` be
real `C^∞` with `f ∼_Δ F X^{-α} Y^{-β} Z^{-γ} x^α y^β z^γ` on
`D ⊆ [X, 2X] × [Y, 2Y] × [Z, 2Z]`, `X ≥ Y ≥ Z`, `XYZ = N`.  Then
`S ≪ N [F N⁻¹ + Z⁻¹ + N^{-1/4} + (F³ X⁴ N⁻⁵)^{1/5} + (F⁶ Δ³ X⁶ N⁻⁸)^{1/8}
       + (Δ Y⁻² Z⁻²)^{1/6} + F^{-1/2} + Y^{-2/5} Z^{-2/5} + (F⁻¹ Y⁻² Z⁻²)^{1/8}]^{1/2} log⁴ N`. -/
def kolesnik_theorem2 : Prop :=
  ∀ (C₀ : ℕ) (α β γ : ℝ),
    α + β + γ ≠ 1 → α + β + γ ≠ 2 →
    α * β * γ * (α - 1) * (β - 1) * (γ - 1) ≠ 0 →
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧
      ∀ (F X Y Z N Δ : ℝ) (D : Set (Fin 3 → ℝ)) (f : (Fin 3 → ℝ) → ℝ),
        0 < Δ → Δ ≤ ε₀ → 0 < F → 1 ≤ Z → Z ≤ Y → Y ≤ X → X * Y * Z = N →
        IsAlgebraicDomain C₀ ![X, Y, Z] D → IsSmooth f →
        ApproxΔ D Δ f (monomial F ![X, Y, Z] ![α, β, γ]) →
        ‖latticeSum D f‖ ≤
          C * (N *
            (F / N + Z⁻¹ + N ^ (-(1 : ℝ) / 4) +
              (F ^ 3 * X ^ 4 * N ^ (-(5 : ℝ))) ^ ((1 : ℝ) / 5) +
              (F ^ 6 * Δ ^ 3 * X ^ 6 * N ^ (-(8 : ℝ))) ^ ((1 : ℝ) / 8) +
              (Δ * Y ^ (-(2 : ℝ)) * Z ^ (-(2 : ℝ))) ^ ((1 : ℝ) / 6) +
              F ^ (-(1 : ℝ) / 2) +
              Y ^ (-(2 : ℝ) / 5) * Z ^ (-(2 : ℝ) / 5) +
              (F⁻¹ * Y ^ (-(2 : ℝ)) * Z ^ (-(2 : ℝ))) ^ ((1 : ℝ) / 8)) ^ ((1 : ℝ) / 2) *
            Real.log N ^ 4)

/-! ### Theorem 3 (`n ≥ 4` variables) -/

/-- **Kolesnik, Theorem 3.**  Let `n ≥ 4` and let `α₁, …, αₙ` be reals with
`α₁ ⋯ αₙ ≠ 0`, `α₁ + ⋯ + αₙ ≠ 2`, `α₁ + α₂ + α₃ ≠ 2` and no subset sum equal
to `1`; let `Δ ≤ ε₀`, `F ≥ X₁²`, `X₁ ≥ ⋯ ≥ Xₙ`, `X₁ ⋯ Xₙ = N`, and let `f` be
real `C^∞` with `f ∼_Δ F X₁^{-α₁} ⋯ Xₙ^{-αₙ} x₁^{α₁} ⋯ xₙ^{αₙ}` on
`D ⊆ ∏ [X_i, 2X_i]`.  Then
`S ≪ N^{1+ε} [ (F^{3n} X₁⁻ⁿ X₂⁻ⁿ X₃⁻ⁿ N⁻⁶)^{1/(n+6)} + X₃⁻¹ (F³ X₁⁻¹ X₂⁻¹)^{1/19}
   + X₂⁻¹ X₃⁻¹ (F¹⁵ X₁⁻⁵)^{1/23} + X₃⁻¹ (F³ Δ⁶ X₁⁻¹ X₂⁻¹)^{1/7}
   + X₂⁻¹ X₃⁻¹ (F⁶ Δ³ X₁⁻²)^{1/8} + N^{-1/(n+1)} + X₃^{-3/4} + √(Δ / X₃) ]^{1/2} log² N`. -/
def kolesnik_theorem3 : Prop :=
  ∀ (n C₀ : ℕ) (α : Fin n → ℝ),
    4 ≤ n → (∏ j, α j) ≠ 0 → (∑ j, α j) ≠ 2 →
    coord α 0 + coord α 1 + coord α 2 ≠ 2 →
    (∀ s : Finset (Fin n), (∑ j ∈ s, α j) ≠ 1) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      ∀ (F Δ : ℝ) (X : Fin n → ℝ) (D : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
        0 < Δ → Δ ≤ ε₀ → (∀ j, 1 ≤ X j) → Antitone X → coord X 0 ^ 2 ≤ F →
        IsAlgebraicDomain C₀ X D → IsSmooth f →
        ApproxΔ D Δ f (monomial F X α) →
        ‖latticeSum D f‖ ≤
          C * (totalProduct X ^ (1 + ε) *
            ((F ^ (3 * n : ℝ) * coord X 0 ^ (-(n : ℝ)) * coord X 1 ^ (-(n : ℝ)) *
                coord X 2 ^ (-(n : ℝ)) * totalProduct X ^ (-(6 : ℝ))) ^ (1 / (n + 6 : ℝ)) +
              (coord X 2)⁻¹ * (F ^ 3 * (coord X 0)⁻¹ * (coord X 1)⁻¹) ^ ((1 : ℝ) / 19) +
              (coord X 1)⁻¹ * (coord X 2)⁻¹ * (F ^ 15 / coord X 0 ^ 5) ^ ((1 : ℝ) / 23) +
              (coord X 2)⁻¹ *
                (F ^ 3 * Δ ^ 6 * (coord X 0)⁻¹ * (coord X 1)⁻¹) ^ ((1 : ℝ) / 7) +
              (coord X 1)⁻¹ * (coord X 2)⁻¹ *
                (F ^ 6 * Δ ^ 3 * coord X 0 ^ (-(2 : ℝ))) ^ ((1 : ℝ) / 8) +
              totalProduct X ^ (-(1 : ℝ) / (n + 1 : ℝ)) +
              coord X 2 ^ (-(3 : ℝ) / 4) +
              Real.sqrt (Δ / coord X 2)) ^ ((1 : ℝ) / 2) *
            Real.log (totalProduct X) ^ 2)

/-! ### The processes `A` and `B` in `n` dimensions (Theorems 4 and 5) -/

/-- Process `B` on exponent tuples (Theorem 4), leading entry:
`λ̃₀ = λ₀ + λ₁ + ⋯ + λ_m - m/2`. -/
noncomputable def processB₀ {n : ℕ} (m : ℕ) (lam₀ : ℝ) (lam : Fin n → ℝ) : ℝ :=
  lam₀ + (∑ j : Fin n, if (j : ℕ) < m then lam j else 0) - (m : ℝ) / 2

/-- Process `B` on exponent tuples (Theorem 4), remaining entries:
`λ̃_j = 1 - λ_j` for `j ≤ m` and `λ̃_j = λ_j` for `j > m`. -/
noncomputable def processBTail {n : ℕ} (m : ℕ) (lam : Fin n → ℝ) : Fin n → ℝ :=
  fun j => if (j : ℕ) < m then 1 - lam j else lam j

/-- **Kolesnik, Theorem 4** (process `B`).  If `m ∈ [1, n]` and
`(λ₀ | λ₁, …, λₙ) ∈ E_n` with `λ_j ≤ 1` for `j ≤ m`, then
`(λ̃₀ | λ̃₁, …, λ̃ₙ) ∈ E_n` with
`λ̃₀ = λ₀ + λ₁ + ⋯ + λ_m - m/2`, `λ̃_j = 1 - λ_j` (`j ≤ m`), `λ̃_j = λ_j`
(`j > m`).  The restriction `λ_j ≤ 1` is not printed in the paper but is
forced by the non-negativity of exponent tuples (`(0 | 2, 1, …, 1) ∈ E_n`
trivially, and the printed statement would produce the entry `-1`).  (The
paper proves this assuming the conjectural inequality (1).) -/
def kolesnik_theorem4 : Prop :=
  ∀ (n m : ℕ) (lam₀ : ℝ) (lam : Fin n → ℝ), 1 ≤ m → m ≤ n →
    (∀ j : Fin n, (j : ℕ) < m → lam j ≤ 1) →
    InExponentClass n lam₀ lam →
    InExponentClass n (processB₀ m lam₀ lam) (processBTail m lam)

/-- Process `A` on exponent tuples (Theorem 5), leading entry:
`λ̃₀ = λ₀ m / (2 (λ₀ + |λ*|))`, `|λ*| = λ₁* + ⋯ + λ_m*`. -/
noncomputable def processA₀ {m : ℕ} (lam₀ : ℝ) (lamStar : Fin m → ℝ) : ℝ :=
  lam₀ * m / (2 * (lam₀ + ∑ i, lamStar i))

/-- Process `A` on exponent tuples (Theorem 5), remaining entries:
`λ̃_j = (λ_j + λ_j* - 1) m / (2 (λ₀ + |λ*|)) + 1/2` for `j ≤ m` and
`λ̃_j = (λ_j - 1) m / (2 (λ₀ + |λ*|)) + 1` for `j > m`. -/
noncomputable def processATail {n m : ℕ} (lam₀ : ℝ) (lam : Fin n → ℝ) (lamStar : Fin m → ℝ) :
    Fin n → ℝ :=
  fun j =>
    if h : (j : ℕ) < m then
      (lam j + lamStar ⟨j, h⟩ - 1) * m / (2 * (lam₀ + ∑ i, lamStar i)) + 1 / 2
    else
      (lam j - 1) * m / (2 * (lam₀ + ∑ i, lamStar i)) + 1

/-- **Kolesnik, Theorem 5** (process `A`).  Let `λ_j ≥ 0` (`j = 0, …, n`),
`m ∈ [1, n]`, `λ_j* ≥ 0` (`j = 1, …, m`), `λ₀ + |λ*| ≥ m`, and
`(λ₀ | λ₁, …, λₙ, λ₁*, …, λ_m*) ∈ E_{m+n}`.  Then `(λ̃₀ | λ̃₁, …, λ̃ₙ) ∈ E_n`
with `λ̃₀ = λ₀ m / (2(λ₀ + |λ*|))`,
`λ̃_j = (λ_j + λ_j* - 1) m / (2(λ₀ + |λ*|)) + 1/2` (`j ≤ m`) and
`λ̃_j = (λ_j - 1) m / (2(λ₀ + |λ*|)) + 1` (`j > m`).  (The paper proves this
assuming the conjectural inequality (4).) -/
def kolesnik_theorem5 : Prop :=
  ∀ (n m : ℕ) (lam₀ : ℝ) (lam : Fin n → ℝ) (lamStar : Fin m → ℝ),
    1 ≤ m → m ≤ n → 0 ≤ lam₀ → (∀ j, 0 ≤ lam j) → (∀ j, 0 ≤ lamStar j) →
    (m : ℝ) ≤ lam₀ + ∑ i, lamStar i →
    InExponentClass (n + m) lam₀ (Fin.append lam lamStar) →
    InExponentClass n (processA₀ lam₀ lamStar) (processATail lam₀ lam lamStar)

/-! ### Numerical corollaries (§1) -/

/-- `ζ(1/2 + it) ⋘ t^θ`: for every `ε > 0` there is `C` with
`|ζ(1/2 + it)| ≤ C t^{θ + ε}` for `t ≥ 2`. -/
def ZetaHalfLineBound (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t →
    ‖riemannZeta ((1 : ℂ) / 2 + (t : ℂ) * Complex.I)‖ ≤ C * t ^ (θ + ε)

/-- **Kolesnik, §1, after Theorem 1**: `ζ(1/2 + it) ⋘ t^{139/858}`
(`139/858 = 0.162004…`). -/
def kolesnik_zetaBound : Prop := ZetaHalfLineBound (139 / 858)

/-- **Kolesnik, §1, after Theorem 1**: the circle-problem error term satisfies
`Δ(R) ≪ R^{139/429}`, with `Δ(R) = ∑_{n ≤ R} r(n) - π R = circleError R`. -/
def kolesnik_circleBound : Prop :=
  ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → |circleError R| ≤ C * R ^ ((139 : ℝ) / 429)

/-- **Kolesnik, §1**: the previously best published unconditional bound
`ζ(1/2 + it) ⋘ t^{35/216}` (Kolesnik 1982, `35/216 = 0.162037…`). -/
def kolesnik1982_zetaBound : Prop := ZetaHalfLineBound (35 / 216)

/-- **Kolesnik, §1** (conditional on Theorems 4 and 5, found by computer):
`(6966/117930 | 99727/117930, 99727/117930) ∈ E₂`. -/
def kolesnik_conditionalTuple₂ : Prop :=
  InExponentClass 2 (6966 / 117930) ![99727 / 117930, 99727 / 117930]

/-- **Kolesnik, §1** (conditional on Theorems 4 and 5):
`(47728/294910 | 1/2) ∈ E₁` (the paper prints the denominator as `274910`,
corrected in the transcription: `47728/294910 = 0.16183920…`). -/
def kolesnik_conditionalTuple₁ : Prop :=
  InExponentClass 1 (47728 / 294910) ![1 / 2]

/-- **Kolesnik, §1** (conditional on Theorems 4 and 5):
`ζ(1/2 + it) ⋘ t^{47728/294910}`, `47728/294910 = 0.16183920…`. -/
def kolesnik_conditionalZetaBound : Prop := ZetaHalfLineBound (47728 / 294910)

/-- The one-dimensional exponent pairs `E` produced by van der Corput's method
of exponent pairs, in the standard normalisation `(κ, λ)` (`f' ≍ F/X`,
`S ≪ (F/X)^κ X^λ`): the closure of the trivial pair `(0, 1)` under the
`A`-process `(κ, λ) ↦ (κ/(2κ+2), 1/2 + λ/(2κ+2))` and the `B`-process
`(κ, λ) ↦ (λ - 1/2, κ + 1/2)`.  Kolesnik's normalisation `S ≪ F^k X^l` has
`(k, l) = (κ, λ - κ)`, so his `2k + l` is `κ + λ`. -/
inductive IsVdCExponentPair : ℝ → ℝ → Prop
  | trivial : IsVdCExponentPair 0 1
  | procA {κ l : ℝ} : IsVdCExponentPair κ l →
      IsVdCExponentPair (κ / (2 * κ + 2)) (1 / 2 + l / (2 * κ + 2))
  | procB {κ l : ℝ} : IsVdCExponentPair κ l →
      IsVdCExponentPair (l - 1 / 2) (κ + 1 / 2)

/-- **Rankin's theorem** as quoted in Kolesnik, §1:
`inf_{(k,l) ∈ E} (2k + l) = 0.829021356…`, i.e. in the standard normalisation
`inf_{(κ,λ) ∈ E} (κ + λ) ∈ [0.829021356, 0.829021357)`. -/
def kolesnik_rankinConstant : Prop :=
  let S : Set ℝ := {s | ∃ κ l : ℝ, IsVdCExponentPair κ l ∧ s = κ + l}
  (0.829021356 : ℝ) ≤ sInf S ∧ sInf S < (0.829021357 : ℝ)

/-- **Kolesnik, §1** (consequence of Rankin's theorem): the one-dimensional
method of exponent pairs cannot give `ζ(1/2 + it) ≪ t^θ` with
`θ < 0.16451067…`; every pair `(κ, λ) ∈ E` yields the exponent
`(κ + λ - 1/2)/2 ≥ 0.16451067`. -/
def kolesnik_rankinZetaLimit : Prop :=
  ∀ κ l : ℝ, IsVdCExponentPair κ l → (0.16451067 : ℝ) ≤ (κ + l - 1 / 2) / 2

end LeanProofs.IntegerPoints
