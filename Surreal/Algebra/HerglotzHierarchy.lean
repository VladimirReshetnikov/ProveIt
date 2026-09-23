import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import Surreal.Algebra.HerglotzNegativeAtom
import Surreal.HahnSeries.LeadingVectorTest

/-!
# The strict Hahn–Herglotz hierarchy: finite and ordinary witnesses

This file proves the algebraic and ordinary-analytic clauses of `herg:thm:hierarchy`, the failure
clause of `herg:thm:harnack` (`herg:eq:harnackfailure`) and the algebraic clauses of
`herg:cor:unitary` in `docs/surcomplex/hahn-herglotz-positivity/article.tex`. The scalar field
`F` is any ordered field (for instance `F_Γ = ℝ((t^Γ))`), `F[i]` is `Complexify F`, and `ε`
plays the role of the positive infinitesimal `t^η`; the Toeplitz-positivity clauses are also
stated over `ℂ((t^Γ))` for any ordered abelian group `Γ`. Over `F` the only hypotheses used on
`ε` are sign conditions (`0 < ε`, `0 ≤ ε` or `ε ≠ 0`), `2ε² < 1`, `4ε ≤ 1 - z z̄` and `nε < 1`
for ordinary `n`.
The model `ε = t^η` of `ℝ((t^Γ))` satisfies the last (`natCast_mul_toLex_single_lt_one`), but
the `F[i]` results are not otherwise instantiated at `F_Γ`, and the Toeplitz witnesses over
`ℂ((t^Γ))` are not connected to them. The formal power series (`harnackSeries`, `n2Series`) and
the rational functions on `F[i]` (`harnackWitness`, `n2Herglotz`) are separate definitions,
related only by the formal identities after multiplication by `1 - z` and `(1 - z)³`; no
evaluation of a series at a point of `F[i]` is formalized.

`herg:thm:hierarchy`.
* `A ⊂ H`, the `2 × 2`-minor step: if `T_N(c) ⪰ 0` against all vectors over `F[i]`, with
  `c_0 = 1` and `c_{-k} = conj(c_k)`, then `1 - c_n conj(c_n) ≥ 0` for `n ≤ N`
  (`normSq_le_one_of_toeplitz_psd`).
* The first three witnesses `c_n = δ_{n0} + t^η bₙ` with `bₙ = -1`, `n²`, `e^{√|n|}` (`n ≠ 0`)
  have `T_N(c) ≻ 0` against all vectors over `ℂ((t^Γ))` for every `N`
  (`negAtomWitness_toeplitz_pos`, `n2Witness_toeplitz_pos`, `expSqrtWitness_toeplitz_pos`),
  by `herg:thm:saturation`.
* `D \ M`: `herg:eq:n2function` as identities of formal power series,
  `(∑ n² zⁿ)(1 - z)³ = z(1 + z)` and `(1 - z)³ H_2 = (1 - z)³ + 2ε z(1 + z)` for
  `H_2 = 1 + 2 ∑ cₙ zⁿ`, `cₙ = εn²`. `herg:eq:n2boundary` by exact algebra in `F[i]`, for the
  rational closed form `H_2(z) = 1 + 2ε z(1 + z)/(1 - z)³` (`n2Herglotz`):
  `z_ε z̄_ε = 1 - 2ε + 2ε²` and `H_2(z_ε) = (2 - ε⁻²) + (3ε⁻¹ - ε⁻² - 1)i`, so for `0 < ε` with
  `2ε² < 1` the point `z_ε` lies in the internal disk, is not a pole, and `Re H_2(z_ε) < 0`.
  The exponent-`η` moments `n²` are unbounded, so they are not the Fourier coefficients of any
  finite signed measure `μ₁ - μ₂` on the unit circle (`n2_not_signed_measure_moments`).
* `A \ D`: the coefficients `e^{√|n|}` violate every polynomial bound of the distribution test
  `herg:eq:distributiontest`, and `∑ e^{√n} zⁿ` converges absolutely for `‖z‖ < 1` and diverges
  for `‖z‖ ≥ 1`, so its radius of convergence is exactly one.
* `H \ A`: `(1 + z)/(1 - z) + εz = 1 + 2 ∑ cₙ zⁿ` as formal power series, with
  `c_1 = 1 + ε/2` and `cₙ = 1` for `n ≥ 2`; `herg:eq:negativeT1`,
  `det T_1 = -ε - ε²/4 < 0`; the form of `T_1` at `(1, -1)` is `-ε`, and `T_1` is not
  positive semidefinite over `F[i]`. The ordinary coefficient `(1 + z)/(1 - z)` has real part
  `(1 - |z|²)/|1 - z|² > 0` at every `z` with `z z̄ < 1`. The rational function
  `f(z) = (1 + z)/(1 - z) + εz` on `F[i]` has `Re f(z) > 0` whenever `0 ≤ ε`, `z z̄ < 1` and
  `4ε ≤ 1 - z z̄` (`re_harnackWitness_pos`); for a positive infinitesimal `ε` this covers every
  point at which `1 - z z̄` exceeds a positive ordinary rational, such as the ordinary points of
  the disk and their infinitesimal perturbations.

`herg:thm:harnack`, failure clause: `f(z) = (1 + z)/(1 - z) + εz` has `f(0) = 1` and
`Re f(r) = (1 + r)/(1 - r) + εr > (1 + r)/(1 - r) · Re f(0)` for `0 < r`, `0 < ε`. The source's
range is `0 < r < 1`; for `r ≥ 1` the statement still holds but is vacuous as a Harnack claim
(the bound is `≤ 0`, reading `2/0 = 0` at `r = 1`).

`herg:cor:unitary`, algebraic clauses, on `V = F[i][ζ, ζ⁻¹]` (Laurent polynomials). On the
circle `conj(p)(ζ) = ∑ conj(pₖ) ζ^{-k}` (`circleConj`), and `Λ_ε(G) = (1 + ε) ∫ G dm - ε G(1)`
(`rieszFunctional`, `herg:eq:Rieszfailure`), where the Haar integral of a trigonometric
polynomial is its constant coefficient. Then `Λ_ε` is `F[i]`-linear, unital and preserves
conjugation, `Λ_ε(ζ^{-n}) = cₙ` for the moments `herg:eq:mainmoments`, the form
`⟨p, q⟩ = Λ_ε(p̄ q)` is Hermitian and sesquilinear, equals
`(1 + ε) ∑ conj(pₖ) qₖ - ε conj(p(1)) q(1)`, and is positive definite when `0 ≤ ε` and
`nε < 1` for every ordinary `n`. Multiplication `U p = ζ p` is a linear equivalence preserving
the form, `Uⁿ 1 = ζⁿ` for `n ∈ ℤ`, the vector `1` is cyclic, `⟨ζʲ, ζᵏ⟩ = c_{j-k}` and
`⟨Uⁿ 1, 1⟩ = cₙ`.

Pending. The five classes `P, M, D, A, H` are not defined here, and the inclusions `P ⊂ M`
(`herg:prop:measuretoeplitz`), `M ⊂ D`, `D ⊂ A` and the analytic part of `A ⊂ H` (finiteness of
`cₙ` in `K_Γ`, vanishing of the negative-exponent coefficients, the classical
Carathéodory–Toeplitz and Herglotz theorems for `H_0`, and transfer to the halo by
`herg:lem:scalar`) remain pending. Of the strictness claims, the following remain pending: that
the `M \ P` witness has no positive coefficientwise measure (uniqueness in
`herg:thm:negativeatom`); that the `D \ M` coefficient distribution is `-δ₀''` of exact order
two, and the `n^{2m}` generalization; that the `A \ D` witness has no periodic distribution (the
necessity half of `herg:thm:representation`); and halo positivity of the `H \ A` witness as a
coherent function (halos and coherent evaluation are not defined here; only the rational
evaluation `re_harnackWitness_pos` is proved). The main comparison of `herg:thm:harnack` is not
proved here, and its failure clause is complete only up to that same point: the witness's
hypothesis `Re f ≥ 0` on ordinary points and on the halo is established only in the form
`re_harnackWitness_pos` for the rational evaluation in `F[i]`, not for `f` as a coherent
function. For `herg:cor:unitary`, the
identification of the Haar integral with the constant coefficient is used as the definition of
`∫ G dm` on trigonometric polynomials (Fourier orthonormality is not rederived), and the absence
of a positive coefficientwise spectral measure remains pending.
-/

namespace Surreal.HerglotzHierarchy

open Surreal.Herglotz Surreal.Complexify

noncomputable section

section PowerSeries

open PowerSeries

variable {R : Type*} [CommRing R]

theorem coeff_zero_one_sub_X_mul (φ : R⟦X⟧) : coeff 0 ((1 - X) * φ) = coeff 0 φ := by
  simp [sub_mul]

theorem coeff_succ_one_sub_X_mul (φ : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) ((1 - X) * φ) = coeff (n + 1) φ - coeff n φ := by
  rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul]

/-- The Cayley series `1 + 2 ∑_{n ≥ 1} zⁿ` of `(1 + z)/(1 - z)`. -/
def cayleySeries : R⟦X⟧ :=
  mk fun n => if n = 0 then 1 else 2

/-- `(1 + z)/(1 - z) = 1 + 2 ∑_{n ≥ 1} zⁿ` as formal power series. -/
theorem one_sub_X_mul_cayleySeries : (1 - X) * (cayleySeries : R⟦X⟧) = 1 + X := by
  ext n
  rcases n with _ | n
  · simp [coeff_zero_one_sub_X_mul, cayleySeries]
  · rw [coeff_succ_one_sub_X_mul]
    rcases n with _ | n
    · simp [cayleySeries, coeff_X]
      norm_num
    · simp [cayleySeries, coeff_X]

/-- `herg:eq:n2function`: `∑ n² zⁿ = z(1 + z)/(1 - z)³` as formal power series. -/
theorem sq_series_mul_one_sub_X_pow_three :
    mk (fun n => (n : R) ^ 2) * (1 - X) ^ 3 = X * (1 + X) := by
  ext n
  rw [mul_comm, pow_three, mul_assoc, mul_assoc]
  rcases n with _ | _ | _ | n
  · simp [coeff_zero_one_sub_X_mul]
  · simp only [zero_add, coeff_succ_one_sub_X_mul, coeff_zero_one_sub_X_mul, coeff_mk]
    simp
  · simp only [coeff_succ_one_sub_X_mul, coeff_zero_one_sub_X_mul, coeff_mk]
    simp [coeff_X]
    norm_num
  · simp only [coeff_succ_one_sub_X_mul, coeff_mk]
    simp only [coeff_succ_X_mul, coeff_one, coeff_X, map_add]
    simp
    ring

end PowerSeries

section Witnesses

open PowerSeries Matrix

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The moments of the Harnack witness `(1 + z)/(1 - z) + εz` of `herg:eq:harnackfailure`:
`c_{±1} = 1 + ε/2` and `c_n = 1` otherwise. -/
def harnackMoment (ε : F) (n : ℤ) : F :=
  if n = 1 ∨ n = -1 then 1 + ε / 2 else 1

/-- The formal power series `1 + 2 ∑_{n ≥ 1} zⁿ + εz`, the Taylor series of
`(1 + z)/(1 - z) + εz` in the formal sense of `one_sub_X_mul_harnackSeries`. -/
def harnackSeries (ε : F) : F⟦X⟧ :=
  cayleySeries + C ε * X

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- `herg:eq:harnackfailure` as a series: `(1 - z) H(z) = 1 + z + εz(1 - z)`, that is,
`H(z) = (1 + z)/(1 - z) + εz`. -/
theorem one_sub_X_mul_harnackSeries (ε : F) :
    (1 - X) * harnackSeries ε = 1 + X + C ε * X * (1 - X) := by
  rw [harnackSeries, mul_add, one_sub_X_mul_cayleySeries]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem coeff_zero_harnackSeries (ε : F) : coeff 0 (harnackSeries ε) = harnackMoment ε 0 := by
  simp [harnackSeries, cayleySeries, harnackMoment]

/-- The Harnack series is `1 + 2 ∑_{n ≥ 1} c_n zⁿ` with the moments `harnackMoment`: its
coefficient of `zⁿ`, `n ≠ 0`, is `2 c_n`. -/
theorem coeff_harnackSeries (ε : F) {n : ℕ} (hn : n ≠ 0) :
    coeff n (harnackSeries ε) = 2 * harnackMoment ε n := by
  rcases n with _ | n
  · exact absurd rfl hn
  · rcases n with _ | n
    · simp [harnackSeries, cayleySeries, harnackMoment]
      ring
    · rw [harnackMoment, if_neg (by omega)]
      simp [harnackSeries, cayleySeries]

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- `herg:thm:hierarchy`, `H \ A`: the first moment is `c_1 = 1 + ε/2`. -/
theorem harnackMoment_one (ε : F) : harnackMoment ε 1 = 1 + ε / 2 := by
  simp [harnackMoment]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem harnackMoment_neg (ε : F) (k : ℤ) : harnackMoment ε (-k) = harnackMoment ε k := by
  unfold harnackMoment
  by_cases h : k = 1 ∨ k = -1
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- `herg:eq:negativeT1`: `det T_1 = 1 - (1 + ε/2)² = -ε - ε²/4`. -/
theorem det_toeplitz_harnackMoment (ε : F) :
    (toeplitz 1 (harnackMoment ε)).det = -ε - ε ^ 2 / 4 := by
  rw [Matrix.det_fin_two]
  simp [toeplitz, harnackMoment]
  ring

/-- `herg:eq:negativeT1`: the determinant is negative for `ε > 0`. -/
theorem det_toeplitz_harnackMoment_neg {ε : F} (hε : 0 < ε) :
    (toeplitz 1 (harnackMoment ε)).det < 0 := by
  rw [det_toeplitz_harnackMoment]
  nlinarith [sq_nonneg ε]

/-- `herg:thm:hierarchy`, `H \ A`: the real quadratic form of `T_1` is `-ε` at `(1, -1)`. -/
theorem harnack_toeplitz_form (ε : F) :
    ![1, -1] ⬝ᵥ (toeplitz 1 (harnackMoment ε) *ᵥ ![1, -1]) = -ε := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, toeplitz, harnackMoment]
  ring

/-- The rational function `(1 + z)/(1 - z) + εz` on `F[i]`. It is a separate definition from
`harnackSeries`; the two are related only by the formal identity `one_sub_X_mul_harnackSeries`. -/
def harnackWitness (ε : F) (z : Complexify F) : Complexify F :=
  (1 + z) / (1 - z) + algebraMap F (Complexify F) ε * z

/-- The normalization `f(0) = 1` of `herg:eq:harnackfailure`. -/
theorem harnackWitness_zero (ε : F) : harnackWitness ε 0 = 1 := by
  simp [harnackWitness]

/-- At a real point, `f(r) = (1 + r)/(1 - r) + εr`. -/
theorem harnackWitness_real (ε r : F) :
    harnackWitness ε (algebraMap F _ r) = algebraMap F _ ((1 + r) / (1 - r) + ε * r) := by
  simp [harnackWitness, map_div₀]

/-- `herg:thm:harnack`, failure clause (`herg:eq:harnackfailure`): at the real point `r > 0`,
`Re f(r) = (1 + r)/(1 - r) + εr` exceeds `(1 + r)/(1 - r) · Re f(0)`, which for `0 < r < 1` is
the sharp classical bound. For `r ≥ 1` the inequality still holds but is not a Harnack statement:
the bound is `≤ 0` (at `r = 1` because Lean reads `2/0` as `0`). The positivity hypothesis on
the witness is `re_harnackWitness_pos`. -/
theorem harnack_sharp_constant_fails {ε r : F} (hε : 0 < ε) (hr : 0 < r) :
    (1 + r) / (1 - r) * (harnackWitness ε 0).re < (harnackWitness ε (algebraMap F _ r)).re := by
  rw [harnackWitness_zero, harnackWitness_real, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.re_one, mul_one]
  linarith [mul_pos hε hr]

/-- The classical input for `H ∈ 𝖧`: `Re((1 + z)/(1 - z)) = (1 - |z|²)/|1 - z|²`. -/
theorem re_cayley (z : Complexify F) :
    ((1 + z) / (1 - z)).re = (1 - normSq z) / normSq (1 - z) := by
  rw [div_eq_mul_inv, mul_re, inv_re, inv_im]
  simp only [normSq, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub,
    QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

/-- The Cayley function has positive real part on the internal unit disk `z z̄ < 1`. -/
theorem re_cayley_pos {z : Complexify F} (hz : normSq z < 1) : 0 < ((1 + z) / (1 - z)).re := by
  rw [re_cayley]
  have h1 : 1 - z ≠ 0 := by
    intro h
    rw [(sub_eq_zero.mp h).symm, normSq_one] at hz
    exact lt_irrefl _ hz
  exact div_pos (by linarith) (normSq_pos h1)

/-- `herg:eq:harnackfailure`, positivity of the witness: the rational function
`f(z) = (1 + z)/(1 - z) + εz` has `Re f(z) > (1 - z z̄)/4 - ε ≥ 0` at every `z` with `z z̄ < 1`
and `4ε ≤ 1 - z z̄`, when `0 ≤ ε`. For a positive infinitesimal `ε` the hypothesis holds at every
point where `1 - z z̄` exceeds a positive ordinary rational. -/
theorem re_harnackWitness_pos {ε : F} (hε : 0 ≤ ε) {z : Complexify F} (hz : normSq z < 1)
    (hεz : 4 * ε ≤ 1 - normSq z) : 0 < (harnackWitness ε z).re := by
  have h1 : 1 - z ≠ 0 := by
    intro h
    rw [(sub_eq_zero.mp h).symm, normSq_one] at hz
    exact lt_irrefl _ hz
  have hD : 0 < normSq (1 - z) := normSq_pos h1
  have hN : z.re ^ 2 + z.im ^ 2 < 1 := hz
  have hD4 : normSq (1 - z) < 4 := by
    simp only [normSq, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one]
    nlinarith [sq_nonneg z.im, sq_nonneg (z.re + 1)]
  have hre1 : -1 < z.re := by nlinarith [sq_nonneg z.im]
  have hq : (1 - normSq z) / 4 < (1 - normSq z) / normSq (1 - z) :=
    div_lt_div_of_pos_left (by linarith) hD hD4
  have hre : (algebraMap F (Complexify F) ε * z).re = ε * z.re := by
    simp [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]
  rw [harnackWitness, QuadraticAlgebra.re_add, re_cayley, hre]
  nlinarith [mul_nonneg hε (by linarith : (0 : F) ≤ z.re + 1)]

/-- `herg:eq:n2moments`: `c_0 = 1` and `c_n = εn²` for `n ≠ 0`. -/
def n2Moment (ε : F) (n : ℤ) : F :=
  if n = 0 then 1 else ε * n ^ 2

/-- The formal power series `1 + 2ε ∑ n² zⁿ` of `H_2`. -/
def n2Series (ε : F) : F⟦X⟧ :=
  mk fun n => if n = 0 then 1 else 2 * ε * n ^ 2

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem coeff_n2Series (ε : F) {n : ℕ} (hn : n ≠ 0) :
    coeff n (n2Series ε) = 2 * n2Moment ε n := by
  simp [n2Series, n2Moment, hn]
  ring

theorem n2Series_eq (ε : F) : n2Series ε = 1 + C (2 * ε) * mk fun n => (n : F) ^ 2 := by
  ext n
  rcases n with _ | n <;> simp [n2Series, mul_assoc]

/-- `herg:eq:n2function`: `(1 - z)³ H_2(z) = (1 - z)³ + 2ε z(1 + z)` as formal power series. -/
theorem one_sub_X_pow_three_mul_n2Series (ε : F) :
    (1 - X) ^ 3 * n2Series ε = (1 - X) ^ 3 + C (2 * ε) * (X * (1 + X)) := by
  rw [n2Series_eq, ← sq_series_mul_one_sub_X_pow_three]
  ring

/-- The closed form `H_2(z) = 1 + 2ε z(1 + z)/(1 - z)³` of `herg:eq:n2function`, as a rational
function on `F[i]`. It is taken as a definition; its only link to `n2Series` is the formal
identity `one_sub_X_pow_three_mul_n2Series`. -/
def n2Herglotz (ε : F) (z : Complexify F) : Complexify F :=
  1 + 2 * algebraMap F (Complexify F) ε * (z * (1 + z)) / (1 - z) ^ 3

/-- The boundary-layer point `z_ε = 1 - (1 + i)ε`. -/
def n2Point (ε : F) : Complexify F :=
  1 - (1 + I) * algebraMap F (Complexify F) ε

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- `herg:eq:n2boundary`: `z_ε z̄_ε = 1 - 2ε + 2ε²`. -/
theorem normSq_n2Point (ε : F) : normSq (n2Point ε) = 1 - 2 * ε + 2 * ε ^ 2 := by
  simp [n2Point, normSq, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem one_sub_n2Point (ε : F) : 1 - n2Point ε = (1 + I) * algebraMap F (Complexify F) ε := by
  rw [n2Point, sub_sub_cancel]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem one_sub_n2Point_ne_zero {ε : F} (hε : ε ≠ 0) : 1 - n2Point ε ≠ 0 := by
  rw [one_sub_n2Point]
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
  exact hε this

/-- `herg:eq:n2boundary`, exact value: `H_2(z_ε) = (2 - ε⁻²) + (3ε⁻¹ - ε⁻² - 1) i`. -/
theorem n2Herglotz_n2Point {ε : F} (hε : ε ≠ 0) :
    n2Herglotz ε (n2Point ε) = ⟨2 - (ε ^ 2)⁻¹, 3 * ε⁻¹ - (ε ^ 2)⁻¹ - 1⟩ := by
  have hD : (1 - n2Point ε) ^ 3 ≠ 0 := pow_ne_zero _ (one_sub_n2Point_ne_zero hε)
  have key : 2 * algebraMap F (Complexify F) ε * (n2Point ε * (1 + n2Point ε)) =
      ((⟨2 - (ε ^ 2)⁻¹, 3 * ε⁻¹ - (ε ^ 2)⁻¹ - 1⟩ : Complexify F) - 1) *
        (1 - n2Point ε) ^ 3 := by
    rw [one_sub_n2Point]
    ext <;> simp [n2Point, pow_succ, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
      field_simp <;> ring
  rw [n2Herglotz, key, mul_div_cancel_right₀ _ hD]
  ring

/-- `herg:eq:n2boundary`: `Re H_2(z_ε) = 2 - ε⁻²`, by exact algebra. -/
theorem re_n2Herglotz_n2Point {ε : F} (hε : ε ≠ 0) :
    (n2Herglotz ε (n2Point ε)).re = 2 - (ε ^ 2)⁻¹ := by
  rw [n2Herglotz_n2Point hε]

/-- `herg:eq:n2boundary`: for `0 < ε` with `2ε² < 1` (in particular for every positive
infinitesimal `ε`), the point `z_ε` lies in the internal disk `z z̄ < 1`, is not a pole of `H_2`,
and `Re H_2(z_ε) < 0`. -/
theorem n2_boundary_negative {ε : F} (hε : 0 < ε) (hε2 : 2 * ε ^ 2 < 1) :
    normSq (n2Point ε) < 1 ∧ 1 - n2Point ε ≠ 0 ∧ (n2Herglotz ε (n2Point ε)).re < 0 := by
  refine ⟨?_, one_sub_n2Point_ne_zero hε.ne', ?_⟩
  · have h1 : ε < 1 := by nlinarith
    rw [normSq_n2Point]
    nlinarith
  · rw [re_n2Herglotz_n2Point hε.ne']
    have h : 2 < 1 / ε ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]
      linarith
    rw [one_div] at h
    linarith

end Witnesses

section Minor

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- The Hermitian form `x* A x = ∑ⱼ ∑ₖ conj(xⱼ) Aⱼₖ xₖ` of a matrix over `F[i]`. -/
def cHermForm {m : Type*} [Fintype m] (A : Matrix m m (Complexify F)) (x : m → Complexify F) :
    Complexify F :=
  ∑ j, ∑ k, star (x j) * A j k * x k

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem star_algebraMap (r : F) :
    star (algebraMap F (Complexify F) r) = algebraMap F (Complexify F) r := by
  ext <;> simp

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem normSq_algebraMap (r : F) : normSq (algebraMap F (Complexify F) r) = r ^ 2 := by
  simp [normSq]

/-- `herg:thm:hierarchy`, the `2 × 2`-minor step of `A ⊂ H`: if `T_N(c) ⪰ 0` against all
vectors over `F[i]`, with `c_0 = 1` and `c_{-k} = conj(c_k)`, then `1 - c_n conj(c_n) ≥ 0` for
every `n ≤ N`. -/
theorem normSq_le_one_of_toeplitz_psd {N : ℕ} (c : ℤ → Complexify F) (h0 : c 0 = 1)
    (hc : ∀ k, c (-k) = star (c k))
    (hpsd : ∀ x : Fin (N + 1) → Complexify F, 0 ≤ (cHermForm (toeplitz N c) x).re)
    {n : ℕ} (hn : n ≤ N) : normSq (c n) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp [h0]
  set i0 : Fin (N + 1) := 0
  set i1 : Fin (N + 1) := ⟨n, by omega⟩
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
    omega
  set x : Fin (N + 1) → Complexify F :=
    fun j => if j = i0 then 1 else if j = i1 then -c n else 0
  have hx0 : x i0 = 1 := by simp [x]
  have hx1 : x i1 = -c n := by simp [x, hne.symm]
  have hxo : ∀ j, j ≠ i0 ∧ j ≠ i1 → x j = 0 := fun j hj => by simp [x, hj.1, hj.2]
  have hrow : ∀ j, ∑ k, star (x j) * toeplitz N c j k * x k =
      star (x j) * toeplitz N c j i0 * x i0 + star (x j) * toeplitz N c j i1 * x i1 :=
    fun j => Fintype.sum_eq_add i0 i1 hne fun k hk => by rw [hxo k hk, mul_zero]
  have hform : cHermForm (toeplitz N c) x =
      algebraMap F (Complexify F) (1 - normSq (c n)) := by
    rw [cHermForm, Fintype.sum_eq_add i0 i1 hne fun j hj => by
      rw [hrow j, hxo j hj]
      simp]
    rw [hrow, hrow, hx0, hx1]
    have e00 : toeplitz N c i0 i0 = 1 := by simp [toeplitz, h0]
    have e11 : toeplitz N c i1 i1 = 1 := by simp [toeplitz, h0]
    have e01 : toeplitz N c i0 i1 = star (c n) := by simp [toeplitz, i0, i1, ← hc]
    have e10 : toeplitz N c i1 i0 = c n := by simp [toeplitz, i0, i1]
    rw [e00, e11, e01, e10, map_sub, map_one, ← star_mul_self_eq, star_one, star_neg]
    ring
  have h := hpsd x
  rw [hform, QuadraticAlgebra.algebraMap_re] at h
  linarith

/-- `herg:thm:hierarchy`, `H \ A`: the Harnack witness violates the `2 × 2` minor test, so
`T_1(c)` is not positive semidefinite over `F[i]` when `ε > 0`. -/
theorem harnack_toeplitz_not_psd {ε : F} (hε : 0 < ε) :
    ¬ ∀ x : Fin 2 → Complexify F, 0 ≤ (cHermForm
      (toeplitz 1 fun n => algebraMap F (Complexify F) (harnackMoment ε n)) x).re := by
  intro h
  have hle := normSq_le_one_of_toeplitz_psd (N := 1)
    (fun n => algebraMap F (Complexify F) (harnackMoment ε n)) (by simp [harnackMoment])
    (fun k => by rw [harnackMoment_neg, star_algebraMap]) h (n := 1) le_rfl
  rw [Nat.cast_one, harnackMoment_one, normSq_algebraMap] at hle
  nlinarith

end Minor

section Unitary

open LaurentPolynomial

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Complex conjugation of a trigonometric polynomial on the circle: since `ζ̄ = ζ⁻¹` there,
`conj(p)(ζ) = ∑ₖ conj(pₖ) ζ^{-k}`. -/
def circleConj (p : (Complexify F)[T;T⁻¹]) : (Complexify F)[T;T⁻¹] :=
  ((invert : (Complexify F)[T;T⁻¹] ≃ₐ[Complexify F] (Complexify F)[T;T⁻¹]).toRingHom.comp
    (AddMonoidAlgebra.mapRingHom ℤ (starRingEnd (Complexify F)))) p

theorem circleConj_mul (p q : (Complexify F)[T;T⁻¹]) :
    circleConj (p * q) = circleConj p * circleConj q :=
  map_mul _ p q

theorem circleConj_add (p q : (Complexify F)[T;T⁻¹]) :
    circleConj (p + q) = circleConj p + circleConj q :=
  map_add _ p q

theorem coeff_circleConj (p : (Complexify F)[T;T⁻¹]) (n : ℤ) :
    (circleConj p).coeff n = star (p.coeff (-n)) := by
  simp [circleConj, starRingEnd_apply]

theorem circleConj_circleConj (p : (Complexify F)[T;T⁻¹]) : circleConj (circleConj p) = p := by
  refine LaurentPolynomial.ext fun n => ?_
  rw [coeff_circleConj, coeff_circleConj, neg_neg, star_star]

theorem circleConj_C (a : Complexify F) : circleConj (C a) = C (star a) := by
  refine LaurentPolynomial.ext fun n => ?_
  rw [coeff_circleConj, C_apply, C_apply]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [if_neg (by omega), if_neg hn, star_zero]

theorem circleConj_T (n : ℤ) : circleConj (T n : (Complexify F)[T;T⁻¹]) = T (-n) := by
  refine LaurentPolynomial.ext fun m => ?_
  rw [coeff_circleConj, T_apply, T_apply]
  by_cases hm : m = -n
  · subst hm
    simp
  · rw [if_neg (by omega), if_neg (by omega), star_zero]

/-- Evaluation at the point `ζ = 1` of the circle. -/
def evalOne (p : (Complexify F)[T;T⁻¹]) : Complexify F :=
  eval₂ (RingHom.id _) 1 p

theorem evalOne_mul (p q : (Complexify F)[T;T⁻¹]) : evalOne (p * q) = evalOne p * evalOne q :=
  map_mul _ p q

theorem evalOne_add (p q : (Complexify F)[T;T⁻¹]) : evalOne (p + q) = evalOne p + evalOne q :=
  map_add _ p q

theorem evalOne_C_mul_T (a : Complexify F) (n : ℤ) : evalOne (C a * T n) = a := by
  simp [evalOne]

theorem evalOne_C (a : Complexify F) : evalOne (C a) = a := by
  simp [evalOne]

theorem evalOne_eq_sum (p : (Complexify F)[T;T⁻¹]) :
    evalOne p = p.coeff.sum fun _ a => a := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [evalOne_add, hp, hq, AddMonoidAlgebra.coeff_add,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  | C_mul_T n a =>
    rw [evalOne_C_mul_T, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.sum_single_index rfl]

theorem evalOne_circleConj (p : (Complexify F)[T;T⁻¹]) :
    evalOne (circleConj p) = star (evalOne p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [circleConj_add, evalOne_add, evalOne_add, hp, hq, star_add]
  | C_mul_T n a => rw [circleConj_mul, circleConj_C, circleConj_T, evalOne_C_mul_T,
      evalOne_C_mul_T]

/-- `herg:eq:Rieszfailure` on `V = F[i][ζ, ζ⁻¹]`: `Λ_ε(G) = (1 + ε) ∫ G dm - ε G(1)`, where the
Haar integral of a trigonometric polynomial is its constant coefficient (`∫ ζⁿ dm = δ_{n0}`). -/
def rieszFunctional (ε : F) : (Complexify F)[T;T⁻¹] →ₗ[Complexify F] Complexify F where
  toFun G := algebraMap F (Complexify F) (1 + ε) * G.coeff 0 -
    algebraMap F (Complexify F) ε * evalOne G
  map_add' G H := by
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, evalOne_add]
    ring
  map_smul' a G := by
    have h1 : (a • G).coeff 0 = a * G.coeff 0 := by simp
    have h2 : evalOne (a • G) = a * evalOne G := by rw [smul_eq_C_mul, evalOne_mul, evalOne_C]
    simp only [h1, h2, RingHom.id_apply, smul_eq_mul]
    ring

theorem rieszFunctional_apply (ε : F) (G : (Complexify F)[T;T⁻¹]) :
    rieszFunctional ε G = algebraMap F (Complexify F) (1 + ε) * G.coeff 0 -
      algebraMap F (Complexify F) ε * evalOne G := rfl

/-- `herg:eq:Rieszfailure`: `Λ_ε(ζ^{-n}) = c_n`, the moments `herg:eq:mainmoments`. -/
theorem rieszFunctional_T_neg (ε : F) (n : ℤ) :
    rieszFunctional ε (T (-n)) = algebraMap F (Complexify F) (negAtomMoment ε n) := by
  have hT : evalOne (T (-n) : (Complexify F)[T;T⁻¹]) = 1 := by simp [evalOne]
  rw [rieszFunctional_apply, hT, T_apply, negAtomMoment]
  by_cases hn : n = 0
  · rw [if_pos (by omega), if_pos hn, map_add, map_one]
    ring
  · rw [if_neg (by omega), if_neg hn, map_neg]
    ring

/-- `herg:thm:functional` (a) for `Λ_ε`, restricted to the trigonometric polynomials
`V = F[i][ζ, ζ⁻¹]`: it is unital. -/
theorem rieszFunctional_one (ε : F) : rieszFunctional ε 1 = 1 := by
  rw [show (1 : (Complexify F)[T;T⁻¹]) = T (-0) by rw [neg_zero, T_zero],
    rieszFunctional_T_neg, negAtomMoment, if_pos rfl, map_one]

/-- `herg:thm:functional` (a) for `Λ_ε`, restricted to the trigonometric polynomials
`V = F[i][ζ, ζ⁻¹]`: it preserves conjugation. -/
theorem rieszFunctional_circleConj (ε : F) (G : (Complexify F)[T;T⁻¹]) :
    rieszFunctional ε (circleConj G) = star (rieszFunctional ε G) := by
  rw [rieszFunctional_apply, rieszFunctional_apply, coeff_circleConj, neg_zero,
    evalOne_circleConj, star_sub, star_mul', star_mul', star_algebraMap, star_algebraMap]

/-- `herg:cor:unitary`: the inner product `⟨p, q⟩ = Λ_ε(p̄ q)` on `V = F[i][ζ, ζ⁻¹]`. -/
def vacuumInner (ε : F) (p q : (Complexify F)[T;T⁻¹]) : Complexify F :=
  rieszFunctional ε (circleConj p * q)

/-- `herg:cor:unitary`: the form is Hermitian. -/
theorem vacuumInner_conj_symm (ε : F) (p q : (Complexify F)[T;T⁻¹]) :
    vacuumInner ε q p = star (vacuumInner ε p q) := by
  rw [vacuumInner, vacuumInner, ← rieszFunctional_circleConj, circleConj_mul,
    circleConj_circleConj, mul_comm]

theorem vacuumInner_add_right (ε : F) (p q q' : (Complexify F)[T;T⁻¹]) :
    vacuumInner ε p (q + q') = vacuumInner ε p q + vacuumInner ε p q' := by
  rw [vacuumInner, mul_add, map_add]
  rfl

theorem vacuumInner_smul_right (ε : F) (a : Complexify F) (p q : (Complexify F)[T;T⁻¹]) :
    vacuumInner ε p (a • q) = a * vacuumInner ε p q := by
  rw [vacuumInner, mul_smul_comm, map_smul, smul_eq_mul]
  rfl

theorem vacuumInner_add_left (ε : F) (p p' q : (Complexify F)[T;T⁻¹]) :
    vacuumInner ε (p + p') q = vacuumInner ε p q + vacuumInner ε p' q := by
  rw [vacuumInner, circleConj_add, add_mul, map_add]
  rfl

theorem vacuumInner_smul_left (ε : F) (a : Complexify F) (p q : (Complexify F)[T;T⁻¹]) :
    vacuumInner ε (a • p) q = star a * vacuumInner ε p q := by
  rw [vacuumInner, smul_eq_C_mul, circleConj_mul, circleConj_C, mul_assoc, ← smul_eq_C_mul,
    map_smul,
    smul_eq_mul]
  rfl

theorem coeff_zero_circleConj_mul (p q : (Complexify F)[T;T⁻¹]) :
    (circleConj p * q).coeff 0 = q.coeff.sum fun k b => star (p.coeff k) * b := by
  rw [AddMonoidAlgebra.coeff_mul_apply_right]
  simp [coeff_circleConj]

/-- `herg:cor:unitary`: explicitly,
`⟨p, q⟩ = (1 + ε) ∑ₖ conj(pₖ) qₖ - ε conj(p(1)) q(1)`. -/
theorem vacuumInner_eq (ε : F) (p q : (Complexify F)[T;T⁻¹]) :
    vacuumInner ε p q = algebraMap F (Complexify F) (1 + ε) *
        (q.coeff.sum fun k b => star (p.coeff k) * b) -
      algebraMap F (Complexify F) ε * (star (evalOne p) * evalOne q) := by
  rw [vacuumInner, rieszFunctional_apply, coeff_zero_circleConj_mul, evalOne_mul,
    evalOne_circleConj]

/-- The Hermitian square `⟨p, p⟩ = (1 + ε) ∑ |pₖ|² - ε |∑ pₖ|²` lies in the real field. -/
theorem vacuumInner_self (ε : F) (p : (Complexify F)[T;T⁻¹]) :
    vacuumInner ε p p = algebraMap F (Complexify F)
      ((1 + ε) * ∑ k ∈ p.coeff.support, normSq (p.coeff k) -
        ε * normSq (∑ k ∈ p.coeff.support, p.coeff k)) := by
  rw [vacuumInner_eq, star_mul_self_eq, evalOne_eq_sum]
  simp only [Finsupp.sum, star_mul_self_eq, ← map_sum, map_sub, map_mul]

theorem normSq_sum_le_card_mul {ι : Type*} (s : Finset ι) (x : ι → Complexify F) :
    normSq (∑ k ∈ s, x k) ≤ s.card * ∑ k ∈ s, normSq (x k) := by
  have hre := sq_sum_le_card_mul_sum_sq (s := s) (f := fun k => (x k).re)
  have him := sq_sum_le_card_mul_sum_sq (s := s) (f := fun k => (x k).im)
  simp only [normSq, re_sum, im_sum, Finset.sum_add_distrib, mul_add]
  linarith

/-- `herg:cor:unitary`: `⟨p, p⟩` is a strictly positive element of `F` for every nonzero `p`
with at most `N + 1` nonzero coefficients, whenever `0 ≤ ε` and `Nε < 1`. -/
theorem vacuumInner_self_pos {ε : F} (hε : 0 ≤ ε) {N : ℕ} (hN : (N : F) * ε < 1)
    {p : (Complexify F)[T;T⁻¹]} (hp : p ≠ 0) (hcard : p.coeff.support.card ≤ N + 1) :
    ∃ r : F, 0 < r ∧ vacuumInner ε p p = algebraMap F (Complexify F) r := by
  refine ⟨_, ?_, vacuumInner_self ε p⟩
  obtain ⟨k, hk⟩ : ∃ k, p.coeff k ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (LaurentPolynomial.ext fun k => by simp [h k])
  set s := p.coeff.support
  have hks : k ∈ s := Finsupp.mem_support_iff.mpr hk
  have hS : 0 < ∑ j ∈ s, normSq (p.coeff j) :=
    lt_of_lt_of_le (normSq_pos hk) (Finset.single_le_sum (fun j _ => normSq_nonneg _) hks)
  have hc : (s.card : F) ≤ N + 1 := by exact_mod_cast hcard
  have h1 : ε * normSq (∑ j ∈ s, p.coeff j) ≤ ε * ((N + 1) * ∑ j ∈ s, normSq (p.coeff j)) :=
    mul_le_mul_of_nonneg_left
      ((normSq_sum_le_card_mul s fun j => p.coeff j).trans
        (mul_le_mul_of_nonneg_right hc hS.le)) hε
  nlinarith [mul_pos (by linarith : (0 : F) < 1 - N * ε) hS]

/-- `herg:cor:unitary`: for an infinitesimal `ε ≥ 0` (`nε < 1` for every ordinary `n`), the form
`⟨p, q⟩ = Λ_ε(p̄ q)` is positive definite. -/
theorem vacuumInner_self_pos_of_infinitesimal {ε : F} (hε : 0 ≤ ε)
    (hinf : ∀ n : ℕ, (n : F) * ε < 1) {p : (Complexify F)[T;T⁻¹]} (hp : p ≠ 0) :
    ∃ r : F, 0 < r ∧ vacuumInner ε p p = algebraMap F (Complexify F) r :=
  vacuumInner_self_pos hε (hinf p.coeff.support.card) hp (Nat.le_succ _)

variable (F) in
/-- `herg:cor:unitary`: the unitary `U p = ζ p`, with inverse `p ↦ ζ⁻¹ p`. -/
def unitaryShift : (Complexify F)[T;T⁻¹] ≃ₗ[Complexify F] (Complexify F)[T;T⁻¹] where
  toFun p := T 1 * p
  invFun p := T (-1) * p
  map_add' p q := mul_add _ p q
  map_smul' a p := mul_smul_comm a (T 1) p
  left_inv p := by
    change T (-1) * (T 1 * p) = p
    rw [← mul_assoc, ← T_add, neg_add_cancel, T_zero, one_mul]
  right_inv p := by
    change T 1 * (T (-1) * p) = p
    rw [← mul_assoc, ← T_add, add_neg_cancel, T_zero, one_mul]

theorem unitaryShift_apply (p : (Complexify F)[T;T⁻¹]) : unitaryShift F p = T 1 * p :=
  rfl

theorem unitaryShift_symm_apply (p : (Complexify F)[T;T⁻¹]) :
    (unitaryShift F).symm p = T (-1) * p :=
  rfl

/-- `Uⁿ p = ζⁿ p` for every integer `n`. -/
theorem unitaryShift_zpow_apply (n : ℤ) :
    ∀ p : (Complexify F)[T;T⁻¹], (unitaryShift F ^ n) p = T n * p := by
  refine Int.induction_on n (fun p => ?_) (fun i ih p => ?_) (fun i ih p => ?_)
  · rw [zpow_zero, T_zero, one_mul]
    rfl
  · rw [zpow_add_one, LinearEquiv.mul_apply, ih, unitaryShift_apply, T_add, mul_assoc]
  · rw [zpow_sub_one, LinearEquiv.mul_apply, ih, T_sub, mul_assoc]
    rfl

/-- `herg:cor:unitary`: `U` preserves the inner product. -/
theorem vacuumInner_unitaryShift (ε : F) (p q : (Complexify F)[T;T⁻¹]) :
    vacuumInner ε (unitaryShift F p) (unitaryShift F q) = vacuumInner ε p q := by
  have hT : (T (-1) : (Complexify F)[T;T⁻¹]) * T 1 = 1 := by
    rw [← T_add, neg_add_cancel, T_zero]
  have h : circleConj (unitaryShift F p) * unitaryShift F q = circleConj p * q := by
    rw [unitaryShift_apply, unitaryShift_apply, circleConj_mul, circleConj_T]
    linear_combination (circleConj p * q) * hT
  rw [vacuumInner, vacuumInner, h]

/-- `herg:cor:unitary`: the vector `1` is cyclic, `span {Uⁿ 1 : n ∈ ℤ} = V`. -/
theorem span_unitaryShift_orbit :
    Submodule.span (Complexify F)
      (Set.range fun n : ℤ => (unitaryShift F ^ n) (1 : (Complexify F)[T;T⁻¹])) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rintro p -
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | C_mul_T n a =>
    rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ a (Submodule.subset_span ⟨n, ?_⟩)
    simp only [unitaryShift_zpow_apply, mul_one]

/-- The Gram matrix of the monomials is the Toeplitz matrix: `⟨ζʲ, ζᵏ⟩ = c_{j-k}`. -/
theorem vacuumInner_T (ε : F) (j k : ℤ) :
    vacuumInner ε (T j) (T k) = algebraMap F (Complexify F) (negAtomMoment ε (j - k)) := by
  rw [vacuumInner, circleConj_T, ← T_add, show -j + k = -(j - k) by ring, rieszFunctional_T_neg]

/-- `herg:cor:unitary`: the vacuum moments are `⟨Uⁿ 1, 1⟩ = c_n`, the moments
`herg:eq:mainmoments`. -/
theorem vacuumInner_unitaryShift_zpow_one (ε : F) (n : ℤ) :
    vacuumInner ε ((unitaryShift F ^ n) 1) 1 =
      algebraMap F (Complexify F) (negAtomMoment ε n) := by
  rw [unitaryShift_zpow_apply, mul_one, ← T_zero, vacuumInner_T, sub_zero]

end Unitary

section Growth

open MeasureTheory Filter

/-- The exponent-`η` coefficients of the witness `herg:eq:superpolynomial`: `0` at `n = 0` and
`e^{√|n|}` for `n ≠ 0`. -/
def expSqrtCoeff (n : ℤ) : ℝ :=
  if n = 0 then 0 else Real.exp (Real.sqrt |(n : ℝ)|)

theorem expSqrtCoeff_neg (n : ℤ) : expSqrtCoeff (-n) = expSqrtCoeff n := by
  simp [expSqrtCoeff]

/-- `e^{√n}` eventually exceeds every polynomial `A (1 + n)^m`. -/
theorem exists_expSqrt_gt (A : ℝ) (m : ℕ) :
    ∃ n : ℕ, 0 < n ∧ A * (1 + n) ^ m < Real.exp (Real.sqrt n) := by
  set K : ℝ := ((2 * m + 2).factorial : ℝ) with hKdef
  obtain ⟨N, hN⟩ := exists_nat_gt (|A| * 2 ^ m * K)
  refine ⟨N + 1, Nat.succ_pos N, ?_⟩
  set x : ℝ := ((N + 1 : ℕ) : ℝ) with hxdef
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hx1 : 1 ≤ x := by
    rw [hxdef]
    push_cast
    linarith
  have hxN : |A| * 2 ^ m * K < x := by
    rw [hxdef]
    push_cast
    linarith
  have hK : 0 < K := by
    rw [hKdef]
    exact_mod_cast Nat.factorial_pos _
  have hexp := Real.pow_div_factorial_le_exp (x := Real.sqrt x) (Real.sqrt_nonneg x) (2 * m + 2)
  have hpow : Real.sqrt x ^ (2 * m + 2) = x ^ (m + 1) := by
    rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, Real.sq_sqrt (by linarith)]
  rw [hpow, ← hKdef] at hexp
  have h1 : A * (1 + x) ^ m ≤ |A| * (2 * x) ^ m :=
    (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) m)
        (abs_nonneg A))
  have h2 : |A| * (2 * x) ^ m < x ^ (m + 1) / K := by
    rw [lt_div_iff₀ hK, mul_pow, pow_succ]
    have hxm : 0 < x ^ m := by positivity
    nlinarith [mul_lt_mul_of_pos_right hxN hxm]
  linarith

/-- `herg:thm:hierarchy`, `A \ D`: the exponent-`η` coefficients `e^{√|n|}` violate every
polynomial bound `|aₙ| ≤ A (1 + |n|)^m` of the distribution test `herg:eq:distributiontest`. -/
theorem expSqrtCoeff_not_polynomially_bounded :
    ¬ ∃ (A : ℝ) (m : ℕ), ∀ n : ℤ, |expSqrtCoeff n| ≤ A * (1 + |(n : ℝ)|) ^ m := by
  rintro ⟨A, m, h⟩
  obtain ⟨n, hn, hlt⟩ := exists_expSqrt_gt A m
  have hb := h n
  rw [expSqrtCoeff, if_neg (by omega), abs_of_pos (Real.exp_pos _), Int.cast_natCast,
    abs_of_nonneg (Nat.cast_nonneg n)] at hb
  linarith

theorem sqrt_le_mul_add_inv {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ c * x + 1 / (4 * c) := by
  set s := Real.sqrt x
  have hs : c * s ^ 2 = c * x := by rw [Real.sq_sqrt hx]
  have e : c * (s - 1 / (2 * c)) ^ 2 = c * s ^ 2 - s + 1 / (4 * c) := by
    field_simp
    ring
  nlinarith [mul_nonneg hc.le (sq_nonneg (s - 1 / (2 * c)))]

theorem summable_expSqrt_mul_pow_of_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun n : ℕ => Real.exp (Real.sqrt n) * r ^ n := by
  have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
  set c : ℝ := -Real.log r / 2 with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    linarith
  set q : ℝ := Real.exp (Real.log r / 2) with hq_def
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (1 / (4 * c))))
  have hs := sqrt_le_mul_add_inv hc (Nat.cast_nonneg (α := ℝ) n)
  have hr : r ^ n = Real.exp (n * Real.log r) := by rw [Real.exp_nat_mul, Real.exp_log hr0]
  have hqn : q ^ n = Real.exp (n * (Real.log r / 2)) := by rw [hq_def, Real.exp_nat_mul]
  calc Real.exp (Real.sqrt n) * r ^ n ≤ Real.exp (c * n + 1 / (4 * c)) * r ^ n := by
        gcongr
    _ = Real.exp (1 / (4 * c)) * q ^ n := by
        rw [hr, hqn, ← Real.exp_add, ← Real.exp_add]
        congr 1
        linear_combination (n : ℝ) * hc_def

theorem summable_expSqrt_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => Real.exp (Real.sqrt n) * r ^ n := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_expSqrt_mul_pow_of_pos (r := (1 + r) / 2) (by linarith) (by linarith))
  gcongr
  linarith

theorem norm_expSqrt_mul_pow (z : ℂ) (n : ℕ) :
    ‖(Real.exp (Real.sqrt n) : ℂ) * z ^ n‖ = Real.exp (Real.sqrt n) * ‖z‖ ^ n := by
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg (Real.exp_pos _).le]

/-- `herg:thm:hierarchy`, `A \ D`: the exponent-`η` coefficient series `∑ e^{√n} zⁿ` converges
absolutely for `‖z‖ < 1`. -/
theorem summable_expSqrt_series {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (Real.exp (Real.sqrt n) : ℂ) * z ^ n :=
  Summable.of_norm (by
    simpa only [norm_expSqrt_mul_pow] using summable_expSqrt_mul_pow (norm_nonneg z) hz)

/-- `herg:thm:hierarchy`, `A \ D`: the series `∑ e^{√n} zⁿ` diverges for `‖z‖ ≥ 1`, so its
radius of convergence is exactly one. -/
theorem not_summable_expSqrt_series {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ¬ Summable fun n : ℕ => (Real.exp (Real.sqrt n) : ℂ) * z ^ n := by
  intro h
  have ht := h.tendsto_atTop_zero.norm
  rw [norm_zero] at ht
  refine absurd (ge_of_tendsto' ht fun n => ?_) (by norm_num : ¬ (1 : ℝ) ≤ 0)
  rw [norm_expSqrt_mul_pow]
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (Real.sqrt_nonneg _)) (one_le_pow₀ hz)

/-- The Fourier moments of a finite measure on the unit circle are bounded by its mass. -/
theorem norm_circleMoment_le {μ : Measure ℂ} [IsFiniteMeasure μ] (hT : ∀ᵐ z ∂μ, ‖z‖ = 1)
    (n : ℤ) : ‖circleMoment μ n‖ ≤ μ.real Set.univ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun z : ℂ => z ^ (-n)) (C := 1)
    (hT.mono fun z hz => by rw [norm_zpow, hz, one_zpow])
  rw [one_mul] at h
  exact h

/-- `herg:thm:hierarchy`, `D \ M`: the exponent-`η` moments `n²` of `H_2` are unbounded, so they
are not the Fourier coefficients of any finite signed measure `μ₁ - μ₂` on the unit circle. -/
theorem n2_not_signed_measure_moments (μ₁ μ₂ : Measure ℂ) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] (h₁ : ∀ᵐ z ∂μ₁, ‖z‖ = 1) (h₂ : ∀ᵐ z ∂μ₂, ‖z‖ = 1) :
    ¬ ∀ n : ℤ, circleMoment μ₁ n - circleMoment μ₂ n = (n : ℂ) ^ 2 := by
  intro h
  obtain ⟨N, hN⟩ := exists_nat_gt (μ₁.real Set.univ + μ₂.real Set.univ)
  have hb := (norm_sub_le _ _).trans
    (add_le_add (norm_circleMoment_le h₁ (N + 1)) (norm_circleMoment_le h₂ (N + 1)))
  rw [h (N + 1)] at hb
  have hnorm : ‖(((N + 1 : ℤ) : ℂ)) ^ 2‖ = ((N : ℝ) + 1) ^ 2 := by
    rw [norm_pow]
    push_cast
    rw [← Nat.cast_one, ← Nat.cast_add, Complex.norm_natCast]
    push_cast
    ring
  rw [hnorm] at hb
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

end Growth

section HahnWitnesses

open _root_.HahnSeries Surreal.HahnSeries

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The model infinitesimal `ε = t^η` (`η > 0`) of `ℝ((t^Γ))` satisfies `nε < 1` for every
ordinary `n`, the hypothesis of `vacuumInner_self_pos_of_infinitesimal`. -/
theorem natCast_mul_toLex_single_lt_one {η : Γ} (hη : 0 < η) (n : ℕ) :
    (n : Lex ℝ⟦Γ⟧) * toLex (single η 1) < 1 := by
  have e : (n : ℝ⟦Γ⟧) * single η (1 : ℝ) = single η (n : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, Nat.cast_succ, add_mul, ih, one_mul, single_add]
  refine (le_abs_self _).trans_lt ?_
  rw [← abs_one (α := Lex ℝ⟦Γ⟧)]
  refine abs_lt_abs_of_orderTop_ofLex ?_
  rw [ofLex_one, orderTop_one, ofLex_mul, ofLex_natCast, ofLex_toLex, e]
  exact lt_of_lt_of_le (WithTop.coe_pos.mpr hη) orderTop_single_le

/-- `herg:thm:hierarchy`, strict Toeplitz positivity of the witnesses: for an ordinary real
even sequence `b`, the moments `c_n = δ_{n0} + t^η bₙ` have `T_N(c) ≻ 0` against all vectors
over `ℂ((t^Γ))`, for every `N` (`herg:thm:saturation`). -/
theorem toeplitz_real_even_witness_pos (b : ℤ → ℝ) (hb : ∀ k, b (-k) = b k) {η : Γ}
    (hη : 0 < η) (N : ℕ) {u : Fin (N + 1) → ℂ⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ complexHermForm
      (toeplitz N fun k => C (if k = 0 then 1 else 0) + single η 1 * C (b k : ℂ)) u =
        complexRealEmbedding r :=
  complex_toeplitz_saturation_pos_single N (fun k => (b k : ℂ))
    (fun k => by rw [hb, Complex.star_def, Complex.conj_ofReal]) hη hu

/-- `herg:thm:hierarchy`, `M \ P`: the negative-atom moments `c_0 = 1`, `cₙ = -t^η` have
strictly positive Toeplitz matrices of every size over `ℂ((t^Γ))`. -/
theorem negAtomWitness_toeplitz_pos {η : Γ} (hη : 0 < η) (N : ℕ)
    {u : Fin (N + 1) → ℂ⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ complexHermForm (toeplitz N fun k =>
      C (if k = 0 then 1 else 0) + single η 1 * C ((if k = 0 then 0 else -1 : ℝ) : ℂ)) u =
        complexRealEmbedding r :=
  toeplitz_real_even_witness_pos _ (fun k => by simp) hη N hu

/-- `herg:thm:hierarchy`, `D \ M`: the moments `c_0 = 1`, `cₙ = t^η n²` (`herg:eq:n2moments`)
have strictly positive Toeplitz matrices of every size over `ℂ((t^Γ))`. -/
theorem n2Witness_toeplitz_pos {η : Γ} (hη : 0 < η) (N : ℕ)
    {u : Fin (N + 1) → ℂ⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ complexHermForm (toeplitz N fun k =>
      C (if k = 0 then 1 else 0) + single η 1 * C (((k : ℝ) ^ 2 : ℝ) : ℂ)) u =
        complexRealEmbedding r :=
  toeplitz_real_even_witness_pos _ (fun k => by rw [Int.cast_neg, neg_sq]) hη N hu

/-- `herg:thm:hierarchy`, `A \ D`: the moments `c_0 = 1`, `cₙ = t^η e^{√|n|}`
(`herg:eq:superpolynomial`) have strictly positive Toeplitz matrices of every size over
`ℂ((t^Γ))`. -/
theorem expSqrtWitness_toeplitz_pos {η : Γ} (hη : 0 < η) (N : ℕ)
    {u : Fin (N + 1) → ℂ⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ complexHermForm (toeplitz N fun k =>
      C (if k = 0 then 1 else 0) + single η 1 * C (expSqrtCoeff k : ℂ)) u =
        complexRealEmbedding r :=
  toeplitz_real_even_witness_pos _ expSqrtCoeff_neg hη N hu

end HahnWitnesses

end

end Surreal.HerglotzHierarchy
