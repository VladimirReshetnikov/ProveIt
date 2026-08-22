import IntegerPoints.ZhaiCao
import Mathlib.NumberTheory.Divisors

/-!
# Wu, *On the primitive circle problem*

Formal statements (no proofs yet) of the results of

> J. Wu, On the primitive circle problem, Monatsh. Math. 135 (2002), 69–81,

transcribed in `Papers/On the Primitive Circle Problem.tex`.  The general
exponential-sum results of his §2 (Lemma 2.1, Theorem 2, Lemmas 2.5–2.7) are
in `IntegerPoints.ExponentialSums`; this module contains the problem-specific
statements: Theorem 1, the reduction to the bilinear sums `ℛ(M, N)` of (1.3),
the regions `𝒜, ℬ, 𝒞, 𝒟`, Propositions 1–4, and the Vaughan identity of
Lemma 4.1.

Every statement is a `Prop`-valued definition; nothing is asserted.

## Notes on the transcription

* Wu's (4.1) is printed with plus signs.  With the coefficients `a_j`, `b_k`
  as defined there, the correct identity (for `n > U`) is
  `μ(n) = -∑_{jk = n, j ≤ U²} a_j - ∑_{jk = n, j > U, k > U} μ(j) b_k`;
  the signs are immaterial for the bounds in the paper, and
  `wu_vaughanIdentity` states the exact identity.
* Lemma 4.1 proper ("the sum can be decomposed into `O(log² N)` sums of
  types I, I′, II") is a procedural statement about the dyadic decomposition
  of that identity; only the identity itself is formalised here.
-/

open scoped BigOperators
open Real Finset Filter Asymptotics

namespace LeanProofs.IntegerPoints

/-! ### §1: the main theorem and the reduction to `ℛ(M, N)` -/

/-- **(1.1)** (unconditional, as printed by Wu):
`V(x) = (6/π) x + O(x^{1/2} exp(-c (log x)^{3/5} / (log log x)^{1/5}))` for
some `c > 0`. -/
def wu_unconditionalBound : Prop :=
  ∃ c : ℝ, 0 < c ∧
    primitiveCircleError =O[atTop] fun x : ℝ =>
      x ^ ((1 : ℝ) / 2) *
        Real.exp (-c * Real.log x ^ ((3 : ℝ) / 5) / Real.log (Real.log x) ^ ((1 : ℝ) / 5))

/-- **Wu, Theorem 1**: if RH is true then `Δ(x) ≪ x^{221/608 + ε}`. -/
def wu_theorem1 : Prop :=
  RiemannHypothesis →
    ∀ ε : ℝ, 0 < ε → primitiveCircleError =O[atTop] fun x : ℝ => x ^ ((221 : ℝ) / 608 + ε)

/-- **Nowak's formula** (Wu, §1; Zhai–Cao, Proposition 2): under RH, for
`1 ≤ y < x^{1/2}`,
`Δ(x) = ∑_{m ≤ y} μ(m) E(x/m²) + O(x^{1/2 + ε} / y^{1/2})`. -/
def wu_nowakFormula : Prop :=
  RiemannHypothesis →
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ x y : ℝ, 2 ≤ x → 1 ≤ y → y < Real.sqrt x →
        |primitiveCircleError x - moebiusCircleErrorSum x y| ≤
          C * (x ^ ((1 : ℝ) / 2 + ε) / y ^ ((1 : ℝ) / 2))

/-- The bound **(1.3)** for `ℛ(M, N)` throughout the square
`M, N ≤ x^{1 - 2θ}`: for every `ε > 0`, `ℛ(M, N) ≪ x^{θ - 1/4 + ε}`
uniformly in `M, N`. -/
def RSumBoundOnSquare (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ x M N : ℝ, 2 ≤ x → 0 < M → M ≤ x ^ (1 - 2 * θ) → 0 < N → N ≤ x ^ (1 - 2 * θ) →
      ‖RSum x M N‖ ≤ C * x ^ (θ - 1 / 4 + ε)

/-- **Wu, §1, reduction**: under RH, (1.3) on the square `M, N ≤ x^{1-2θ}`
implies `Δ(x) ≪ x^{θ + ε}`.  Wu states this for `θ = 221/608`; the
derivation (Nowak's formula with `y = x^{1-2θ}` and the truncated Voronoi
formula) is uniform for `1/3 ≤ θ < 1/2`. -/
def wu_reductionToRSum : Prop :=
  ∀ θ : ℝ, 1 / 3 ≤ θ → θ < 1 / 2 → RSumBoundOnSquare θ →
    RiemannHypothesis →
      ∀ ε : ℝ, 0 < ε → primitiveCircleError =O[atTop] fun x : ℝ => x ^ (θ + ε)

/-! ### The regions `𝒜(θ), ℬ(θ), 𝒞(θ), 𝒟(θ)` -/

/-- `(M, N) ∈ 𝒜(θ)`: `M ≤ x^{20θ-7}`, `x^{3-8θ} ≤ N ≤ x^{1-2θ}`. -/
def regionA (θ x M N : ℝ) : Prop :=
  0 < M ∧ 0 < N ∧ M ≤ x ^ (20 * θ - 7) ∧ x ^ (3 - 8 * θ) ≤ N ∧ N ≤ x ^ (1 - 2 * θ)

/-- `(M, N) ∈ ℬ(θ)`: `x^{20θ-7} ≤ M ≤ x^{1-2θ}`, `x^{3-8θ} ≤ N ≤ x^{1-2θ}`. -/
def regionB (θ x M N : ℝ) : Prop :=
  0 < M ∧ 0 < N ∧ x ^ (20 * θ - 7) ≤ M ∧ M ≤ x ^ (1 - 2 * θ) ∧
    x ^ (3 - 8 * θ) ≤ N ∧ N ≤ x ^ (1 - 2 * θ)

/-- `(M, N) ∈ 𝒞(θ)`: `M ≤ x^{1-2θ}`, `N ≤ x^{3-8θ}`, `M² N⁻¹ ≤ x^{4θ-1}`
(inside the square `M, N ≤ x^{1-2θ}`). -/
def regionC (θ x M N : ℝ) : Prop :=
  0 < M ∧ 0 < N ∧ M ≤ x ^ (1 - 2 * θ) ∧ N ≤ x ^ (1 - 2 * θ) ∧
    N ≤ x ^ (3 - 8 * θ) ∧ M ^ 2 * N⁻¹ ≤ x ^ (4 * θ - 1)

/-- `(M, N) ∈ 𝒟(θ)`: `M ≤ x^{1-2θ}`, `M² N⁻¹ ≥ x^{4θ-1}`
(inside the square `M, N ≤ x^{1-2θ}`). -/
def regionD (θ x M N : ℝ) : Prop :=
  0 < M ∧ 0 < N ∧ M ≤ x ^ (1 - 2 * θ) ∧ N ≤ x ^ (1 - 2 * θ) ∧
    x ^ (4 * θ - 1) ≤ M ^ 2 * N⁻¹

/-- The bound (1.3) for `ℛ(M, N)` on a region `R` of the `(M, N)`-plane. -/
def RSumBoundOn (θ : ℝ) (R : ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, ∀ x M N : ℝ, 2 ≤ x → R θ x M N → ‖RSum x M N‖ ≤ C * x ^ (θ - 1 / 4 + ε)

/-! ### §3–§4, Propositions 1–4 -/

/-- **Wu, Proposition 1**: for `13/36 ≤ θ ≤ 4/11` and `(M, N) ∈ 𝒜(θ)`,
`ℛ(M, N) ≪ x^{θ - 1/4 + ε}`. -/
def wu_prop1 : Prop :=
  ∀ θ : ℝ, 13 / 36 ≤ θ → θ ≤ 4 / 11 → RSumBoundOn θ regionA

/-- **Wu, Proposition 2**: for `17/47 ≤ θ ≤ 4/11` and `(M, N) ∈ ℬ(θ)`,
`ℛ(M, N) ≪ x^{θ - 1/4 + ε}`. -/
def wu_prop2 : Prop :=
  ∀ θ : ℝ, 17 / 47 ≤ θ → θ ≤ 4 / 11 → RSumBoundOn θ regionB

/-- **Wu, Proposition 3**: for `5/14 ≤ θ ≤ 1/2` and `(M, N) ∈ 𝒞(θ)`,
`ℛ(M, N) ≪ x^{θ - 1/4 + ε}`. -/
def wu_prop3 : Prop :=
  ∀ θ : ℝ, 5 / 14 ≤ θ → θ ≤ 1 / 2 → RSumBoundOn θ regionC

/-- **Wu, Proposition 4**: for `θ = 221/608` and `(M, N) ∈ 𝒟(θ)`,
`ℛ(M, N) ≪ x^{θ - 1/4 + ε}`. -/
def wu_prop4 : Prop := RSumBoundOn (221 / 608) regionD

/-! ### §4, Lemma 4.1: the Vaughan identity for `μ` -/

open Classical in
/-- `a_j = ∑_{dl = j, d ≤ U, l ≤ U} μ(d) μ(l)`. -/
noncomputable def vaughanA (U : ℝ) (j : ℕ) : ℤ :=
  ∑ d ∈ j.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U ∧ ((j / d : ℕ) : ℝ) ≤ U),
    ArithmeticFunction.moebius d * ArithmeticFunction.moebius (j / d)

open Classical in
/-- `b_k = ∑_{d ∣ k, d ≤ U} μ(d)`. -/
noncomputable def vaughanB (U : ℝ) (k : ℕ) : ℤ :=
  ∑ d ∈ k.divisors.filter (fun d : ℕ => (d : ℝ) ≤ U), ArithmeticFunction.moebius d

open Classical in
/-- **Vaughan's identity for `μ`** (pointwise form, with the signs
corrected): for `n > U ≥ 1`,
`μ(n) = -∑_{jk = n, j ≤ U²} a_j - ∑_{jk = n, j > U, k > U} μ(j) b_k`. -/
def wu_vaughanIdentity_pointwise : Prop :=
  ∀ (U : ℝ) (n : ℕ), 1 ≤ U → U < n →
    ArithmeticFunction.moebius n =
      -(∑ j ∈ n.divisors.filter (fun j : ℕ => (j : ℝ) ≤ U ^ 2), vaughanA U j) -
        ∑ j ∈ n.divisors.filter (fun j : ℕ => U < (j : ℝ) ∧ U < ((n / j : ℕ) : ℝ)),
          ArithmeticFunction.moebius j * vaughanB U (n / j)

open Classical in
/-- **Wu, (4.1)** (Montgomery–Vaughan, (11); signs corrected): for
`1 ≤ U ≤ N` and any `f`,
`∑_{n ∼ N} μ(n) f(n) = -∑_{j ≤ U²} ∑_{k ∼ N/j} a_j f(jk)
                       - ∑_{j > U, k > U, jk ∼ N} μ(j) b_k f(jk)`. -/
def wu_vaughanIdentity : Prop :=
  ∀ (U N : ℝ) (f : ℕ → ℂ), 1 ≤ U → U ≤ N →
    ∑ n ∈ dyadic N, moebiusC n * f n =
      -(∑ j ∈ upTo (U ^ 2), ∑ k ∈ dyadic (N / j), (vaughanA U j : ℂ) * f (j * k)) -
        ∑ j ∈ upTo (2 * N), ∑ k ∈ (upTo (2 * N)).filter
            (fun k : ℕ => U < (j : ℝ) ∧ U < (k : ℝ) ∧ j * k ∈ dyadic N),
          moebiusC j * (vaughanB U k : ℂ) * f (j * k)

end LeanProofs.IntegerPoints
