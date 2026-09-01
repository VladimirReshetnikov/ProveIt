import FabiusFunction.Arithmetic
import FabiusFunction.QPochhammerDissection
import FabiusFunction.QPochhammerElementaryIdentities
import FabiusFunction.ScaledInfiniteProducts
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The infinite q-Pochhammer symbol

This module develops the infinite `q`-shifted factorial

`(a;q)_∞ = ∏' j, (1 - a q^j)`

in the generality in which each statement is true, rather than over `ℂ`
alone.

* **Convergence and algebra** hold in every complete normed commutative ring
  with `‖1‖ = 1`, for every nome with `‖q‖ < 1`: the factors are
  multipliable, the finite symbols `(a;q)_n` converge to `(a;q)_∞`, the
  concatenation law `(a;q)_∞ = (a;q)_n (a q^n ; q)_∞` holds, and the product
  dissects into residue classes, `(a;q)_∞ = ∏_{s<r} (a q^s ; q^r)_∞`.
* **Zeros** are characterized in every such ring whose norm is
  multiplicative: `(a;q)_∞ = 0` exactly when some factor vanishes, that is,
  when `a q^j = 1` for some `j`.  In a field with `q ≠ 0` the zeros of
  `a ↦ (a;q)_∞` are therefore exactly the points `q^{-j}`.
* **Regularity in the parameter.**  Over a complete, locally compact normed
  field the product converges locally uniformly in `a`, so `a ↦ (a;q)_∞` is
  continuous; over `ℂ` it is entire.  Everything here is a specialization
  of the scaled-product engine of `ScaledInfiniteProducts` to the factor
  `w ↦ 1 - w` at the scales `q^j`.
* **Simplicity of the zeros.**  Removing the `j`-th factor exhibits
  `(a;q)_∞ = (1 - a q^j) · (a;q)_j · (a q^{j+1}; q)_∞`.  At `a = q^{-j}` the
  cofactor is `(q^{-j};q)_j (q;q)_∞ ≠ 0`, so the derivative there is
  `-q^j (q^{-j};q)_j (q;q)_∞ = (-1)^{j+1} q^{-C(j,2)} (q;q)_j (q;q)_∞ ≠ 0`:
  every zero is simple, with an explicit nonzero derivative.

## Main declarations

* `qPochhammerInfIn`: the symbol in an arbitrary topological commutative ring.
* `multipliable_one_sub_mul_pow_of_norm_lt_one`,
  `hasProd_qPochhammerInfIn`, `tendsto_finiteQPochhammerIn_qPochhammerInfIn`.
* `qPochhammerInfIn_eq_finite_mul_shift`, `qPochhammerInfIn_succ_shift`,
  `qPochhammerInfIn_eq_factor_mul`, `qPochhammerInfIn_dissection`.
* `qPochhammerInfIn_ne_zero`, `qPochhammerInfIn_eq_zero_iff`,
  `qPochhammerInfIn_eq_zero_iff_exists_inv_pow`, `qPochhammerInfIn_self_ne_zero`.
* `hasProdLocallyUniformly_qPochhammerInfIn`, `continuous_qPochhammerInfIn`,
  `differentiable_qPochhammerInfIn`.
* `hasDerivAt_qPochhammerInfIn_of_mul_pow_eq_one`,
  `hasDerivAt_qPochhammerInfIn_inv_pow`, `deriv_qPochhammerInfIn_inv_pow_ne_zero`.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

noncomputable section

/-- The infinite `q`-Pochhammer symbol `(a;q)_∞ = ∏' j, (1 - a q^j)`, in an
arbitrary topological commutative ring.  When the factors are not
multipliable this is Mathlib's junk value `1`; every theorem below records the
contraction hypothesis `‖q‖ < 1` under which the product genuinely
converges. -/
def qPochhammerInfIn {R : Type*} [CommRing R] [TopologicalSpace R]
    (a q : R) : R :=
  ∏' j : ℕ, (1 - a * q ^ j)

/-- The defining infinite product of `qPochhammerInfIn`. -/
theorem qPochhammerInfIn_eq_tprod {R : Type*} [CommRing R] [TopologicalSpace R]
    (a q : R) :
    qPochhammerInfIn a q = ∏' j : ℕ, (1 - a * q ^ j) := rfl

/-! ## Absolute summability of the factor deviations -/

section Summability

variable {R : Type*} [NormedRing R] [NormOneClass R]

/-- The deviations `a q^j` of the factors from `1` are absolutely summable
for every contracting nome, in any normed ring with `‖1‖ = 1`. -/
theorem summable_norm_mul_pow (a : R) {q : R} (hq : ‖q‖ < 1) :
    Summable fun j : ℕ => ‖a * q ^ j‖ := by
  have hgeom : Summable fun j : ℕ => ‖a‖ * ‖q‖ ^ j :=
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖a‖
  refine hgeom.of_nonneg_of_le (fun j => norm_nonneg _) fun j => ?_
  calc ‖a * q ^ j‖ ≤ ‖a‖ * ‖q ^ j‖ := norm_mul_le _ _
    _ ≤ ‖a‖ * ‖q‖ ^ j :=
      mul_le_mul_of_nonneg_left (norm_pow_le q j) (norm_nonneg a)

/-- A factor `1 - x` cannot vanish once `‖x‖ < 1`. -/
theorem one_sub_ne_zero_of_norm_lt_one {x : R} (hx : ‖x‖ < 1) :
    1 - x ≠ 0 := by
  intro h
  have hx1 : x = 1 := (sub_eq_zero.mp h).symm
  rw [hx1, norm_one] at hx
  exact lt_irrefl _ hx

/-- For a contracting nome, `‖q · q^j‖ < 1` for every `j`. -/
theorem norm_mul_pow_self_lt_one {q : R} (hq : ‖q‖ < 1) (j : ℕ) :
    ‖q * q ^ j‖ < 1 := by
  calc ‖q * q ^ j‖ ≤ ‖q‖ * ‖q ^ j‖ := norm_mul_le _ _
    _ ≤ ‖q‖ * ‖q‖ ^ j :=
      mul_le_mul_of_nonneg_left (norm_pow_le q j) (norm_nonneg q)
    _ ≤ ‖q‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg q) hq.le) (norm_nonneg q)
    _ < 1 := by simpa using hq

end Summability

section FiniteNonvanishing

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [NoZeroDivisors R]

/-- No factor of `(q;q)_n` vanishes for a contracting nome, so neither does
the finite product. -/
theorem finiteQPochhammerIn_self_ne_zero {q : R} (hq : ‖q‖ < 1) (n : ℕ) :
    finiteQPochhammerIn q q n ≠ 0 := by
  haveI : Nontrivial R := ⟨⟨1, 0, fun h => by
    have h' := congrArg norm h
    rw [norm_one, norm_zero] at h'
    exact one_ne_zero h'⟩⟩
  unfold finiteQPochhammerIn
  exact Finset.prod_ne_zero_iff.mpr fun j _ =>
    one_sub_ne_zero_of_norm_lt_one (norm_mul_pow_self_lt_one hq j)

end FiniteNonvanishing

/-! ## Convergence in a complete normed commutative ring -/

section Convergence

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R]

/-- **Multipliability.**  For `‖q‖ < 1` the factors `1 - a q^j` are
multipliable, because their deviations from `1` are absolutely summable. -/
theorem multipliable_one_sub_mul_pow_of_norm_lt_one (a : R) {q : R}
    (hq : ‖q‖ < 1) :
    Multipliable fun j : ℕ => 1 - a * q ^ j := by
  have hsum : Summable fun j : ℕ => ‖-(a * q ^ j)‖ := by
    simpa only [norm_neg] using summable_norm_mul_pow a hq
  exact (multipliable_one_add_of_summable hsum).congr fun j => by ring

/-- The factors `1 - a q^j` have product `(a;q)_∞`. -/
theorem hasProd_qPochhammerInfIn (a : R) {q : R} (hq : ‖q‖ < 1) :
    HasProd (fun j : ℕ => 1 - a * q ^ j) (qPochhammerInfIn a q) :=
  (multipliable_one_sub_mul_pow_of_norm_lt_one a hq).hasProd

/-- **Finite symbols converge to the infinite one.**  The `n`-th finite
symbol `(a;q)_n` is literally the `n`-th partial product. -/
theorem tendsto_finiteQPochhammerIn_qPochhammerInfIn (a : R) {q : R}
    (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => finiteQPochhammerIn a q n) atTop
      (𝓝 (qPochhammerInfIn a q)) := by
  simpa only [finiteQPochhammerIn, qPochhammerInfIn] using
    (multipliable_one_sub_mul_pow_of_norm_lt_one a hq).tendsto_prod_tprod_nat

/-- **Concatenation.**  `(a;q)_∞ = (a;q)_n · (a q^n ; q)_∞`: the infinite
product splits after any finite prefix, exactly as the finite symbols do. -/
theorem qPochhammerInfIn_eq_finite_mul_shift (a : R) {q : R} (hq : ‖q‖ < 1)
    (n : ℕ) :
    qPochhammerInfIn a q =
      finiteQPochhammerIn a q n * qPochhammerInfIn (a * q ^ n) q := by
  -- the infinite concatenation is the limit of the finite one
  have h2 : Tendsto
      (fun N : ℕ => finiteQPochhammerIn a q n * finiteQPochhammerIn (a * q ^ n) q N) atTop
      (𝓝 (finiteQPochhammerIn a q n * qPochhammerInfIn (a * q ^ n) q)) :=
    (tendsto_finiteQPochhammerIn_qPochhammerInfIn (a * q ^ n) hq).const_mul _
  refine tendsto_nhds_unique ?_ h2
  have h1 : Tendsto (fun N : ℕ => finiteQPochhammerIn a q (N + n)) atTop
      (𝓝 (qPochhammerInfIn a q)) :=
    (tendsto_finiteQPochhammerIn_qPochhammerInfIn a hq).comp (tendsto_add_atTop_nat n)
  refine h1.congr fun N => ?_
  rw [add_comm, finiteQPochhammerIn_add]

/-- Peeling the first factor: `(a;q)_∞ = (1 - a) · (a q ; q)_∞`. -/
theorem qPochhammerInfIn_succ_shift (a : R) {q : R} (hq : ‖q‖ < 1) :
    qPochhammerInfIn a q = (1 - a) * qPochhammerInfIn (a * q) q := by
  simpa [finiteQPochhammerIn] using qPochhammerInfIn_eq_finite_mul_shift a hq 1

/-- **Removing one factor.**  For every `j`,
`(a;q)_∞ = (1 - a q^j) · ((a;q)_j · (a q^{j+1} ; q)_∞)`.  The cofactor is the
product of all the factors other than the `j`-th one. -/
theorem qPochhammerInfIn_eq_factor_mul (a : R) {q : R} (hq : ‖q‖ < 1) (j : ℕ) :
    qPochhammerInfIn a q =
      (1 - a * q ^ j) *
        (finiteQPochhammerIn a q j * qPochhammerInfIn (a * q ^ (j + 1)) q) := by
  rw [qPochhammerInfIn_eq_finite_mul_shift a hq (j + 1), finiteQPochhammerIn_succ]
  ring

/-- **Dissection into residue classes.**  For `0 < r`,
`(a;q)_∞ = ∏_{s<r} (a q^s ; q^r)_∞`.  It is the limit along the multiples of
`r` of the finite dissection `finiteQPochhammerIn_dissection`. -/
theorem qPochhammerInfIn_dissection (a : R) {q : R} (hq : ‖q‖ < 1) {r : ℕ}
    (hr : 0 < r) :
    qPochhammerInfIn a q =
      ∏ s ∈ Finset.range r, qPochhammerInfIn (a * q ^ s) (q ^ r) := by
  have hqr : ‖q ^ r‖ < 1 :=
    lt_of_le_of_lt (norm_pow_le q r) (pow_lt_one₀ (norm_nonneg q) hq hr.ne')
  have hmul : Tendsto (fun n : ℕ => r * n) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b =>
      ⟨b, fun n hn => hn.trans (Nat.le_mul_of_pos_left n hr)⟩
  have h1 : Tendsto (fun n : ℕ => finiteQPochhammerIn a q (r * n)) atTop
      (𝓝 (qPochhammerInfIn a q)) :=
    (tendsto_finiteQPochhammerIn_qPochhammerInfIn a hq).comp hmul
  have h2 : Tendsto
      (fun n : ℕ => ∏ s ∈ Finset.range r, finiteQPochhammerIn (a * q ^ s) (q ^ r) n)
      atTop (𝓝 (∏ s ∈ Finset.range r, qPochhammerInfIn (a * q ^ s) (q ^ r))) :=
    tendsto_finsetProd _ fun s _ =>
      tendsto_finiteQPochhammerIn_qPochhammerInfIn (a * q ^ s) hqr
  refine tendsto_nhds_unique h1 ?_
  simpa only [finiteQPochhammerIn_dissection] using h2

end Convergence

/-! ## The zero set -/

section ZeroSet

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
  [NormMulClass R]

/-- **No hidden zeros.**  If no factor vanishes, neither does the product. -/
theorem qPochhammerInfIn_ne_zero (a : R) {q : R} (hq : ‖q‖ < 1)
    (h : ∀ j : ℕ, a * q ^ j ≠ 1) :
    qPochhammerInfIn a q ≠ 0 := by
  have hsum : Summable fun j : ℕ => ‖-(a * q ^ j)‖ := by
    simpa only [norm_neg] using summable_norm_mul_pow a hq
  have hne : ∀ j : ℕ, 1 + -(a * q ^ j) ≠ 0 := fun j => by
    rw [← sub_eq_add_neg, sub_ne_zero]
    exact fun h' => h j h'.symm
  have := tprod_one_add_ne_zero_of_summable hne hsum
  simpa only [qPochhammerInfIn, ← sub_eq_add_neg] using this

/-- **The zero set.**  `(a;q)_∞ = 0` exactly when some factor `1 - a q^j`
vanishes, that is, when `a q^j = 1` for some `j`. -/
theorem qPochhammerInfIn_eq_zero_iff (a : R) {q : R} (hq : ‖q‖ < 1) :
    qPochhammerInfIn a q = 0 ↔ ∃ j : ℕ, a * q ^ j = 1 := by
  constructor
  · intro h0
    by_contra hnone
    exact qPochhammerInfIn_ne_zero a hq (fun j hj => hnone ⟨j, hj⟩) h0
  · rintro ⟨j, hj⟩
    exact tprod_of_exists_eq_zero ⟨j, show 1 - a * q ^ j = 0 by rw [hj, sub_self]⟩

/-- `(q;q)_∞ ≠ 0` for every contracting nome. -/
theorem qPochhammerInfIn_self_ne_zero {q : R} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q ≠ 0 := by
  refine qPochhammerInfIn_ne_zero q hq fun j h => ?_
  have h1 : ‖q * q ^ j‖ < 1 := norm_mul_pow_self_lt_one hq j
  rw [h, norm_one] at h1
  exact lt_irrefl _ h1

end ZeroSet

/-! ## Parameter dependence over a normed field -/

section NormedFieldElementary

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The symbol `(a;q)_∞` is the scaled product of the factor `w ↦ 1 - w` at
the scales `q^j`; this is the form consumed by `ScaledInfiniteProducts`. -/
theorem qPochhammerInfIn_eq_tprod_smul (a q : 𝕜) :
    qPochhammerInfIn a q = ∏' j : ℕ, (1 - (q ^ j) • a) := by
  refine tprod_congr fun j => ?_
  rw [smul_eq_mul, mul_comm]

/-- The scale norms `‖q^j‖` are summable for `‖q‖ < 1`. -/
theorem summable_norm_pow_of_norm_lt_one {q : 𝕜} (hq : ‖q‖ < 1) :
    Summable fun j : ℕ => ‖q ^ j‖ := by
  simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg q) hq

/-- The factor `w ↦ 1 - w` deviates from `1` linearly at the origin. -/
theorem isBigO_one_sub_sub_one :
    (fun w : 𝕜 => (1 - w) - 1) =O[𝓝 0] fun w : 𝕜 => w := by
  simp only [sub_sub_cancel_left]
  exact (Asymptotics.isBigO_refl (fun w : 𝕜 => w) (𝓝 0)).neg_left

end NormedFieldElementary

/-- The finite symbol `a ↦ (a;q)_n` is a polynomial in `a`, hence
differentiable over every nontrivially normed field. -/
theorem differentiable_finiteQPochhammerIn {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (q : 𝕜) (n : ℕ) :
    Differentiable 𝕜 fun a : 𝕜 => finiteQPochhammerIn a q n := by
  induction n with
  | zero =>
      simp only [finiteQPochhammerIn_zero]
      exact differentiable_const 1
  | succ n ih =>
      simp only [finiteQPochhammerIn_succ]
      exact ih.mul ((differentiable_const 1).sub (differentiable_id.mul_const _))

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- In a field with `q ≠ 0`, the zeros of `a ↦ (a;q)_∞` are exactly the
points `q^{-j}`, `j = 0, 1, 2, …`. -/
theorem qPochhammerInfIn_eq_zero_iff_exists_inv_pow (a : 𝕜) {q : 𝕜} (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) :
    qPochhammerInfIn a q = 0 ↔ ∃ j : ℕ, a = (q ^ j)⁻¹ := by
  rw [qPochhammerInfIn_eq_zero_iff a hq]
  refine exists_congr fun j => ⟨fun h => eq_inv_of_mul_eq_one_left h, fun h => ?_⟩
  rw [h]
  exact inv_mul_cancel₀ (pow_ne_zero j hq0)

/-- **Locally uniform convergence in the parameter.**  Over a complete,
locally compact normed field the products `(a;q)_n` converge to `(a;q)_∞`
locally uniformly in `a`. -/
theorem hasProdLocallyUniformly_qPochhammerInfIn [LocallyCompactSpace 𝕜]
    {q : 𝕜} (hq : ‖q‖ < 1) :
    HasProdLocallyUniformly (fun (j : ℕ) (a : 𝕜) => 1 - a * q ^ j)
      (fun a => qPochhammerInfIn a q) := by
  have h : HasProdLocallyUniformly (fun (j : ℕ) (a : 𝕜) => 1 - (q ^ j) • a)
      (fun a => ∏' j : ℕ, (1 - (q ^ j) • a)) :=
    hasProdLocallyUniformly_scaled (fun w : 𝕜 => 1 - w) (fun j => q ^ j)
      (summable_norm_pow_of_norm_lt_one hq) isBigO_one_sub_sub_one
      (continuous_const.sub continuous_id)
  have hf : (fun (j : ℕ) (a : 𝕜) => 1 - (q ^ j) • a) =
      fun (j : ℕ) (a : 𝕜) => 1 - a * q ^ j := by
    funext j a
    rw [smul_eq_mul, mul_comm]
  have hg : (fun a : 𝕜 => ∏' j : ℕ, (1 - (q ^ j) • a)) =
      fun a => qPochhammerInfIn a q := by
    funext a
    exact (qPochhammerInfIn_eq_tprod_smul a q).symm
  rwa [hf, hg] at h

/-- `a ↦ (a;q)_∞` is continuous over a complete, locally compact normed
field. -/
theorem continuous_qPochhammerInfIn [LocallyCompactSpace 𝕜] {q : 𝕜} (hq : ‖q‖ < 1) :
    Continuous fun a : 𝕜 => qPochhammerInfIn a q := by
  have h : Continuous fun a : 𝕜 => ∏' j : ℕ, (1 - (q ^ j) • a) :=
    continuous_tprod_scaled (fun w : 𝕜 => 1 - w) (fun j => q ^ j)
      (summable_norm_pow_of_norm_lt_one hq) isBigO_one_sub_sub_one
      (continuous_const.sub continuous_id)
  have hg : (fun a : 𝕜 => ∏' j : ℕ, (1 - (q ^ j) • a)) =
      fun a => qPochhammerInfIn a q := by
    funext a
    exact (qPochhammerInfIn_eq_tprod_smul a q).symm
  rwa [hg] at h

end NormedField

/-- The cofactor `(q^{-j};q)_j` in closed form:
`(q^{-j};q)_j = (-1)^j q^{-C(j+1,2)} (q;q)_j`, written without negative
exponents as `q^{j²} (q^{-j};q)_j = (-1)^j q^{C(j,2)} (q;q)_j`. -/
theorem pow_sq_mul_finiteQPochhammerIn_inv_pow_self {𝕜 : Type*} [Field 𝕜] {q : 𝕜}
    (hq0 : q ≠ 0) (j : ℕ) :
    q ^ (j * j) * finiteQPochhammerIn (q ^ j)⁻¹ q j =
      (-1 : 𝕜) ^ j * q ^ j.choose 2 * finiteQPochhammerIn q q j := by
  have h := pow_mul_finiteQPochhammerIn_inv_pow_eq q hq0 (le_refl j)
  simpa only [Nat.sub_self, zero_add, pow_one] using h

/-! ## Entire dependence on the parameter over `ℂ`, and simple zeros -/

section Complex

/-- **`a ↦ (a;q)_∞` is entire** for every complex nome with `‖q‖ < 1`. -/
theorem differentiable_qPochhammerInfIn {q : ℂ} (hq : ‖q‖ < 1) :
    Differentiable ℂ fun a : ℂ => qPochhammerInfIn a q := by
  have h : Differentiable ℂ fun a : ℂ => ∏' j : ℕ, (1 - (q ^ j) • a) :=
    differentiable_tprod_scaled_of_eq_one (fun w : ℂ => 1 - w) (fun j => q ^ j)
      (summable_norm_pow_of_norm_lt_one hq)
      ((differentiable_const 1).sub differentiable_id) (by simp)
  have hg : (fun a : ℂ => ∏' j : ℕ, (1 - (q ^ j) • a)) =
      fun a => qPochhammerInfIn a q := by
    funext a
    exact (qPochhammerInfIn_eq_tprod_smul a q).symm
  rwa [hg] at h

/-- **Derivative at a zero.**  If `a₀ q^j = 1`, then
`(a;q)_∞ = (1 - a q^j) · g(a)` with `g(a) = (a;q)_j (a q^{j+1}; q)_∞`, and the
first factor vanishes at `a₀`; hence the derivative at `a₀` is
`-q^j · g(a₀)`. -/
theorem hasDerivAt_qPochhammerInfIn_of_mul_pow_eq_one {q : ℂ} (hq : ‖q‖ < 1)
    (j : ℕ) {a₀ : ℂ} (h₀ : a₀ * q ^ j = 1) :
    HasDerivAt (fun a : ℂ => qPochhammerInfIn a q)
      (-(q ^ j) * (finiteQPochhammerIn a₀ q j * qPochhammerInfIn (a₀ * q ^ (j + 1)) q))
      a₀ := by
  have hfun : (fun a : ℂ => qPochhammerInfIn a q) =
      fun a => (1 - a * q ^ j) *
        (finiteQPochhammerIn a q j * qPochhammerInfIn (a * q ^ (j + 1)) q) := by
    funext a
    exact qPochhammerInfIn_eq_factor_mul a hq j
  rw [hfun]
  have h1 : HasDerivAt (fun a : ℂ => 1 - a * q ^ j) (-(q ^ j)) a₀ := by
    simpa using ((hasDerivAt_id a₀).mul_const (q ^ j)).const_sub 1
  have hg : DifferentiableAt ℂ
      (fun a : ℂ => finiteQPochhammerIn a q j * qPochhammerInfIn (a * q ^ (j + 1)) q) a₀ :=
    ((differentiable_finiteQPochhammerIn q j).mul
      ((differentiable_qPochhammerInfIn hq).comp (differentiable_id.mul_const _))) a₀
  have h := h1.mul hg.hasDerivAt
  beta_reduce at h
  rw [h₀, sub_self, zero_mul, add_zero] at h
  exact h

/-- **Every zero is simple, with an explicit derivative.**  At `a = q^{-j}`,
`d/da (a;q)_∞ = (-1)^{j+1} q^{-C(j,2)} (q;q)_j (q;q)_∞`. -/
theorem hasDerivAt_qPochhammerInfIn_inv_pow {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (j : ℕ) :
    HasDerivAt (fun a : ℂ => qPochhammerInfIn a q)
      ((-1 : ℂ) ^ (j + 1) * (q ^ j.choose 2)⁻¹ *
        finiteQPochhammerIn q q j * qPochhammerInfIn q q)
      (q ^ j)⁻¹ := by
  have hqj : q ^ j ≠ 0 := pow_ne_zero j hq0
  have h₀ : (q ^ j)⁻¹ * q ^ j = 1 := inv_mul_cancel₀ hqj
  have h := hasDerivAt_qPochhammerInfIn_of_mul_pow_eq_one hq j h₀
  have hshift : (q ^ j)⁻¹ * q ^ (j + 1) = q := by
    rw [pow_succ, ← mul_assoc, h₀, one_mul]
  rw [hshift] at h
  convert h using 1
  -- the exponent bookkeeping `j² = j + 2·C(j,2)`
  have hsq : q ^ (j * j) = q ^ j * (q ^ j.choose 2) ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    have h2 := Fabius.two_mul_choose_two_add j
    rw [sq] at h2
    omega
  have hc : q ^ j.choose 2 ≠ 0 := pow_ne_zero _ hq0
  have hcof := pow_sq_mul_finiteQPochhammerIn_inv_pow_self hq0 j
  rw [hsq] at hcof
  have hcof' : q ^ j * q ^ j.choose 2 * finiteQPochhammerIn (q ^ j)⁻¹ q j =
      (-1 : ℂ) ^ j * finiteQPochhammerIn q q j := by
    apply mul_left_cancel₀ hc
    linear_combination hcof
  have hinv : (q ^ j.choose 2)⁻¹ * q ^ j.choose 2 = 1 := inv_mul_cancel₀ hc
  linear_combination
    ((q ^ j.choose 2)⁻¹ * qPochhammerInfIn q q) * hcof' +
      (-(q ^ j * finiteQPochhammerIn (q ^ j)⁻¹ q j * qPochhammerInfIn q q)) * hinv

/-- The derivative of `a ↦ (a;q)_∞` at the zero `q^{-j}` is nonzero: the
zero is simple. -/
theorem deriv_qPochhammerInfIn_inv_pow_ne_zero {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (j : ℕ) :
    (-1 : ℂ) ^ (j + 1) * (q ^ j.choose 2)⁻¹ *
        finiteQPochhammerIn q q j * qPochhammerInfIn q q ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · exact pow_ne_zero _ (by norm_num)
  · exact inv_ne_zero (pow_ne_zero _ hq0)
  · exact finiteQPochhammerIn_self_ne_zero hq j
  · exact qPochhammerInfIn_self_ne_zero hq

end Complex

end

end Fabius
