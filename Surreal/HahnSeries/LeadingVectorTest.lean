import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Algebra.Polynomial.Roots
import Surreal.Algebra.HerglotzNegativeAtom
import Surreal.HahnSeries.ComplexNumbers
import Surreal.HahnSeries.StandardPart
import Surreal.HahnSeries.StrongMeasure

/-!
# The leading-vector test and Toeplitz saturation

This file proves `herg:lem:leadingvector` and the finite-matrix clauses of
`herg:thm:saturation` in `docs/surcomplex/hahn-herglotz-positivity/article.tex`.

`herg:lem:leadingvector`. Let `A` be a Hermitian matrix with entries of nonnegative
valuation in `K_Γ` whose standard part `st A` is positive definite over the coefficients. Then
`u* A u` is a strictly positive element of `F_Γ` for every nonzero Hahn vector `u`. The proof is
the source's: write `u = t^β w` with `β` the least coordinate valuation, so that `w` is finite
with nonzero standard part `x`. Then `u* A u = t^{2β} w* A w`, and the standard part of
`w* A w` is `x* (st A) x > 0`. The reduction `twistedForm_leading` is proved once for any
coefficient field and any coefficientwise ring endomorphism of the Hahn field. It is then
specialized three ways:
* `leadingVector`: `K_Γ = R[i]((t^Γ))` for any ordered field `R`, which is `ℂ((t^Γ))` for
  `R = ℝ` up to `Complexify ℝ ≃ ℂ`;
* `leadingVector_complex` and `leadingVector_posDef`: native `ℂ((t^Γ))`, the latter with the
  hypothesis `st A ≻ 0` stated as Mathlib's `Matrix.PosDef`;
* `leadingVector_real`: real quadratic forms over `R((t^Γ))`, where no symmetry is needed.
In `leadingVector` and `leadingVector_complex`, only positivity of the real part of the ordinary
form of `st A` is assumed, which `st A ≻ 0` implies; `leadingVector_posDef` assumes
`Matrix.PosDef`, and `leadingVector_real` assumes positivity of the real quadratic form of
`st A`. The value group is any ordered abelian group; no divisibility is used.

`herg:thm:saturation`, finite-matrix clauses.
* First statement (`complex_toeplitz_saturation_pos_single`): for ordinary `b_n ∈ ℂ` with
  `b_{-n} = conj(b_n)`, no growth condition, and `ε = t^η` with `η > 0`, the moments
  `c_n = δ_{n0} + ε b_n` have `T_N(c) ≻ 0` against all Hahn vectors for every `N`. This holds for
  every real infinitesimal `ε` (`complex_toeplitz_saturation_pos`), and over `R[i]((t^Γ))`
  (`toeplitz_saturation_pos`, `toeplitz_saturation_pos_single`). The normalization `b_0 = 0`
  is not needed for positivity.
* General statement (`toeplitz_measure_perturbation_pos`): the Fourier moments
  `c_n = ∫ ζ^{-n} dμ` of an ordinary finite positive measure on the unit circle with infinite
  support keep `T_N(c + d) ≻ 0` for every entrywise positive-valuation perturbation `d` with
  `d_{-n} = conj(d_n)`. The circle measure is a finite Borel measure on `ℂ`, concentrated almost
  everywhere on `‖ζ‖ = 1`, whose Mathlib support is infinite. Its classical input,
  `toeplitz_circleMoment_posDef`, is proved by writing the Toeplitz form as
  `∫ |∑ xₖ ζ^k|² dμ` and noting that a nonzero polynomial has finitely many zeros. The algebraic
  form, for any ordinary conjugate-symmetric moments with positive definite `T_N`, is
  `complex_toeplitz_perturbation_pos` (and `toeplitz_perturbation_pos` over `R[i]((t^Γ))`).

In these saturation theorems, `T_N(c) ≻ 0` is stated as strict positivity of `u* T_N(c) u` in
`F_Γ` for every nonzero Hahn vector `u`. The Hermitian half of `≻ 0` is `toeplitz_hermitian`.

Pending: the second sentence of the first statement of `herg:thm:saturation`, that every finite
prefix of the moments `δ_{n0} + ε b_n` is represented by the positive coefficientwise Hahn
probability measure `(1 + ε q_N) m` on the circle. It needs coefficientwise Hahn measures and
Haar measure on the circle, and is not formalized here.
-/

namespace Surreal.Herglotz

open _root_.HahnSeries Surreal.HahnSeries Finset

noncomputable section

section Generic

variable {Γ K n : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]
  [Fintype n]

/-- The twisted quadratic form `∑ᵢ ∑ⱼ σ(uᵢ) Aᵢⱼ uⱼ`. For coefficientwise conjugation `σ` it is
the Hermitian form `u* A u`; for `σ = id` it is the quadratic form `uᵀ A u`. -/
def twistedForm (σ : K⟦Γ⟧ →+* K⟦Γ⟧) (A : Matrix n n K⟦Γ⟧) (u : n → K⟦Γ⟧) : K⟦Γ⟧ :=
  ∑ i, ∑ j, σ (u i) * A i j * u j

/-- A nonzero Hahn vector is `t^β` times a vector of nonnegative valuation whose standard part is
nonzero, where `β` is the least valuation of a coordinate. This is the normalization in the proof
of `herg:lem:leadingvector`. -/
theorem exists_single_mul_leading {u : n → K⟦Γ⟧} (hu : u ≠ 0) :
    ∃ (β : Γ) (w : n → K⟦Γ⟧), (∀ i, u i = single β 1 * w i) ∧
      (∀ i, 0 ≤ (w i).orderTop) ∧ (fun i => (w i).coeff 0) ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu
  have hne : (univ : Finset n).Nonempty := ⟨i₀, mem_univ _⟩
  obtain ⟨i₁, -, hi₁⟩ := exists_mem_eq_inf' hne fun i => (u i).orderTop
  have hmin : ∀ i, (u i₁).orderTop ≤ (u i).orderTop := fun i =>
    hi₁ ▸ inf'_le (fun i => (u i).orderTop) (mem_univ i)
  have hu₁ : u i₁ ≠ 0 := by
    intro h
    have h₀ := hmin i₀
    rw [h, orderTop_zero, top_le_iff, orderTop_eq_top] at h₀
    exact hi₀ h₀
  obtain ⟨β, hβ⟩ := WithTop.ne_top_iff_exists.mp (orderTop_ne_top.2 hu₁)
  refine ⟨β, fun i => single (-β) 1 * u i, fun i => ?_, fun i => ?_, ?_⟩
  · rw [← mul_assoc, single_mul_single, add_neg_cancel, mul_one, single_zero_one, one_mul]
  · refine le_orderTop_iff_forall.mpr fun g hg => ?_
    rw [coeff_single_mul, one_mul]
    apply coeff_eq_zero_of_lt_orderTop
    have hg0 : g < 0 := by exact_mod_cast hg
    refine lt_of_lt_of_le ?_ (hβ ▸ hmin i)
    exact WithTop.coe_lt_coe.mpr (by rw [sub_neg_eq_add]; exact add_lt_of_neg_left β hg0)
  · intro h
    have h₁ := congrFun h i₁
    simp only [Pi.zero_apply] at h₁
    rw [coeff_single_mul, one_mul, zero_sub, neg_neg] at h₁
    exact coeff_orderTop_ne hβ.symm h₁

/-- A coefficientwise ring endomorphism fixes the monomials `t^β`. -/
theorem map_single_one_of_coeff (σ : K⟦Γ⟧ →+* K⟦Γ⟧) (τ : K →+* K)
    (hσ : ∀ z g, (σ z).coeff g = τ (z.coeff g)) (β : Γ) : σ (single β 1) = single β 1 := by
  apply _root_.HahnSeries.ext
  funext g
  rw [hσ]
  by_cases hg : g = β
  · subst hg
    rw [coeff_single_same, map_one]
  · rw [coeff_single_of_ne hg, map_zero]

/-- A coefficientwise ring endomorphism maps constants to constants. -/
theorem map_C_of_coeff (σ : K⟦Γ⟧ →+* K⟦Γ⟧) (τ : K →+* K)
    (hσ : ∀ z g, (σ z).coeff g = τ (z.coeff g)) (a : K) : σ (C a) = C (τ a) := by
  apply _root_.HahnSeries.ext
  funext g
  rw [hσ, C_apply, C_apply]
  by_cases hg : g = 0
  · subst hg
    rw [coeff_single_same, coeff_single_same]
  · rw [coeff_single_of_ne hg, coeff_single_of_ne hg, map_zero]

/-- A coefficientwise ring endomorphism preserves nonnegative valuation. -/
theorem orderTop_nonneg_of_coeff (σ : K⟦Γ⟧ →+* K⟦Γ⟧) (τ : K →+* K)
    (hσ : ∀ z g, (σ z).coeff g = τ (z.coeff g)) {z : K⟦Γ⟧} (hz : 0 ≤ z.orderTop) :
    0 ≤ (σ z).orderTop :=
  le_orderTop_iff_forall.mpr fun g hg => by
    rw [hσ, coeff_eq_zero_of_lt_orderTop (hg.trans_le hz), map_zero]

/-- Scaling the vector by `t^β` scales the form by `t^(2β)`. -/
theorem twistedForm_single_mul (σ : K⟦Γ⟧ →+* K⟦Γ⟧) {β : Γ} (hσ : σ (single β 1) = single β 1)
    (A : Matrix n n K⟦Γ⟧) (w : n → K⟦Γ⟧) :
    twistedForm σ A (fun i => single β 1 * w i) = single (β + β) 1 * twistedForm σ A w := by
  have h2 : single (β + β) (1 : K) = single β 1 * single β 1 := by
    rw [single_mul_single, mul_one]
  rw [twistedForm, twistedForm, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [map_mul, hσ, h2]
  ring

/-- On finite matrices and finite vectors the form is finite, and its standard part is the
ordinary twisted form of the standard parts. -/
theorem twistedForm_nonneg_coeff_zero (σ : K⟦Γ⟧ →+* K⟦Γ⟧) (τ : K →+* K)
    (hσ : ∀ z g, (σ z).coeff g = τ (z.coeff g)) (A : Matrix n n K⟦Γ⟧)
    (hA : ∀ i j, 0 ≤ (A i j).orderTop) (w : n → K⟦Γ⟧) (hw : ∀ i, 0 ≤ (w i).orderTop) :
    0 ≤ (twistedForm σ A w).orderTop ∧
      (twistedForm σ A w).coeff 0 =
        ∑ i, ∑ j, τ ((w i).coeff 0) * (A i j).coeff 0 * (w j).coeff 0 := by
  have hσw : ∀ i, 0 ≤ (σ (w i)).orderTop := fun i => orderTop_nonneg_of_coeff σ τ hσ (hw i)
  have hterm : ∀ i j, 0 ≤ (σ (w i) * A i j).orderTop := fun i j => by
    rw [orderTop_mul]
    exact add_nonneg (hσw i) (hA i j)
  refine ⟨(mem_nonnegativeSubring _).mp ?_, ?_⟩
  · refine sum_mem fun i _ => sum_mem fun j _ => ?_
    exact mul_mem ((mem_nonnegativeSubring _).mpr (hterm i j))
      ((mem_nonnegativeSubring _).mpr (hw j))
  · rw [twistedForm, coeff_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [coeff_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [coeff_zero_mul_of_nonnegative _ _ (hterm i j) (hw j),
      coeff_zero_mul_of_nonnegative _ _ (hσw i) (hA i j), hσ]

/-- For an involution `σ` and a `σ`-Hermitian matrix, the form is `σ`-fixed. -/
theorem twistedForm_map_eq (σ : K⟦Γ⟧ →+* K⟦Γ⟧) (hinv : ∀ z, σ (σ z) = z)
    (A : Matrix n n K⟦Γ⟧) (hA : ∀ i j, σ (A i j) = A j i) (u : n → K⟦Γ⟧) :
    σ (twistedForm σ A u) = twistedForm σ A u := by
  simp only [twistedForm, map_sum, map_mul, hinv, hA]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

/-- The leading-vector reduction of `herg:lem:leadingvector`: `u^σ A u = t^(2β) y`, where `y` is
finite and its standard part is the ordinary form of `st A` at a nonzero ordinary vector. -/
theorem twistedForm_leading (σ : K⟦Γ⟧ →+* K⟦Γ⟧) (τ : K →+* K)
    (hσ : ∀ z g, (σ z).coeff g = τ (z.coeff g)) (A : Matrix n n K⟦Γ⟧)
    (hA : ∀ i j, 0 ≤ (A i j).orderTop) {u : n → K⟦Γ⟧} (hu : u ≠ 0) :
    ∃ (β : Γ) (w : n → K⟦Γ⟧) (x : n → K), x ≠ 0 ∧
      twistedForm σ A u = single (β + β) 1 * twistedForm σ A w ∧
      0 ≤ (twistedForm σ A w).orderTop ∧
      (twistedForm σ A w).coeff 0 = ∑ i, ∑ j, τ (x i) * (A i j).coeff 0 * x j := by
  obtain ⟨β, w, huw, hw, hx⟩ := exists_single_mul_leading hu
  obtain ⟨h0, hc⟩ := twistedForm_nonneg_coeff_zero σ τ hσ A hA w hw
  refine ⟨β, w, fun i => (w i).coeff 0, hx, ?_, h0, hc⟩
  rw [show u = fun i => single β 1 * w i from funext huw]
  exact twistedForm_single_mul σ (map_single_one_of_coeff σ τ hσ β) A w

end Generic

section Toeplitz

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]
  (N : ℕ) (c : ℤ → K) (d : ℤ → K⟦Γ⟧)

/-- Toeplitz matrices of ordinary moments plus finite perturbations have finite entries. -/
theorem orderTop_toeplitz_nonneg (hd : ∀ k, 0 ≤ (d k).orderTop) (i j : Fin (N + 1)) :
    0 ≤ ((toeplitz N fun k => C (c k) + d k) i j).orderTop := by
  rw [toeplitz, Matrix.of_apply]
  refine le_trans (le_min ?_ (hd _)) min_orderTop_le_orderTop_add
  rw [C_apply]
  exact orderTop_single_le

/-- With infinitesimal perturbations, the standard part is the ordinary Toeplitz matrix. -/
theorem coeff_zero_toeplitz (hd : ∀ k, 0 < (d k).orderTop) (i j : Fin (N + 1)) :
    ((toeplitz N fun k => C (c k) + d k) i j).coeff 0 = c ((i : ℤ) - j) := by
  rw [toeplitz, Matrix.of_apply, coeff_add, C_apply, coeff_single_same,
    (coeff_zero_eq_zero_iff_orderTop_pos _ (hd _).le).mpr (hd _), add_zero]

/-- Conjugate symmetry of the moments and of the perturbation makes the Toeplitz matrix
`σ`-Hermitian. -/
theorem toeplitz_hermitian (σ : K⟦Γ⟧ →+* K⟦Γ⟧) (τ : K →+* K)
    (hσ : ∀ z g, (σ z).coeff g = τ (z.coeff g)) (hc : ∀ k, τ (c k) = c (-k))
    (hds : ∀ k, σ (d k) = d (-k)) (i j : Fin (N + 1)) :
    σ ((toeplitz N fun k => C (c k) + d k) i j) = (toeplitz N fun k => C (c k) + d k) j i := by
  simp only [toeplitz, Matrix.of_apply, map_add, hds, map_C_of_coeff σ τ hσ, hc, neg_sub]

end Toeplitz

section Positivity

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  [LinearOrder R] [IsStrictOrderedRing R]

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- Positive monomials: `t^g > 0`. -/
theorem toLex_single_one_pos (g : Γ) : 0 < toLex (single g (1 : R)) :=
  pos_of_coeff (i := g) (fun _ hj => coeff_single_of_ne hj.ne)
    (by rw [coeff_single_same]; exact one_pos)

omit [IsOrderedAddMonoid Γ] [IsStrictOrderedRing R] in
/-- A finite series with positive standard part is positive. -/
theorem toLex_pos_of_coeff_zero {y : R⟦Γ⟧} (h0 : 0 ≤ y.orderTop) (hpos : 0 < y.coeff 0) :
    0 < toLex y :=
  pos_of_coeff (i := 0)
    (fun _ hj => coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hj) h0))
    hpos

variable {n : Type*} [Fintype n]

/-- The real form of `herg:lem:leadingvector`: if `A` has finite entries in `R((t^Γ))` and the
quadratic form of its standard part is positive definite, then `uᵀ A u > 0` for every nonzero
Hahn vector `u`. No symmetry of `A` is needed. -/
theorem leadingVector_real (A : Matrix n n R⟦Γ⟧) (hA : ∀ i j, 0 ≤ (A i j).orderTop)
    (hst : ∀ x : n → R, x ≠ 0 → 0 < x ⬝ᵥ (A.map (fun a => a.coeff 0)).mulVec x)
    {u : n → R⟦Γ⟧} (hu : u ≠ 0) : 0 < toLex (u ⬝ᵥ A.mulVec u) := by
  have hform : u ⬝ᵥ A.mulVec u = twistedForm (RingHom.id _) A u := by
    simp only [twistedForm, dotProduct, Matrix.mulVec, RingHom.id_apply, mul_sum, mul_assoc]
  obtain ⟨β, w, x, hx, hscale, h0, hc⟩ :=
    twistedForm_leading (RingHom.id _) (RingHom.id R) (fun _ _ => rfl) A hA hu
  rw [hform, hscale, toLex_mul]
  refine mul_pos (toLex_single_one_pos _) (toLex_pos_of_coeff_zero h0 ?_)
  rw [hc]
  simpa only [dotProduct, Matrix.mulVec, Matrix.map_apply, RingHom.id_apply, mul_sum,
    mul_assoc] using hst x hx

end Positivity

section Complexify

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]
  [LinearOrder R] [IsStrictOrderedRing R] {n : Type*} [Fintype n]

/-- The Hermitian form `u* A u = ∑ᵢ ∑ⱼ conj(uᵢ) Aᵢⱼ uⱼ` over `K_Γ = R[i]((t^Γ))`. -/
def hahnHermForm (A : Matrix n n (Complexify R)⟦Γ⟧) (u : n → (Complexify R)⟦Γ⟧) :
    (Complexify R)⟦Γ⟧ :=
  ∑ i, ∑ j, conjugation (u i) * A i j * u j

/-- Coefficientwise conjugation as a ring homomorphism. -/
def conjugationHom : (Complexify R)⟦Γ⟧ →+* (Complexify R)⟦Γ⟧ := conjugation.toRingHom

omit [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] theorem conjugationHom_apply (z : (Complexify R)⟦Γ⟧) :
    conjugationHom z = conjugation z := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem coeff_conjugationHom (z : (Complexify R)⟦Γ⟧) (g : Γ) :
    (conjugationHom z).coeff g = starRingEnd (Complexify R) (z.coeff g) := rfl

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem embedRealSeries_single_one (g : Γ) :
    embedRealSeries (single g (1 : R)) = single g 1 := by
  apply _root_.HahnSeries.ext
  funext h
  rw [coeff_embedRealSeries]
  by_cases hh : h = g
  · subst hh
    rw [coeff_single_same, coeff_single_same, map_one]
  · rw [coeff_single_of_ne hh, coeff_single_of_ne hh, map_zero]

/-- A finite conjugation-fixed series whose standard part has positive real part is a positive
element of the real Hahn field. -/
theorem exists_embedRealSeries_pos {y : (Complexify R)⟦Γ⟧} (hy : conjugation y = y)
    (h0 : 0 ≤ y.orderTop) (hpos : 0 < (y.coeff 0).re) :
    ∃ r : R⟦Γ⟧, 0 < toLex r ∧ y = embedRealSeries r := by
  obtain ⟨r, rfl⟩ := (conjugation_eq_self_iff_mem_range y).mp hy
  refine ⟨r, pos_of_coeff (i := 0) (fun j hj => ?_) ?_, rfl⟩
  · have h := coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hj) h0)
    simpa using congrArg QuadraticAlgebra.re h
  · simpa using hpos

/-- `herg:lem:leadingvector`, over `K_Γ = R[i]((t^Γ))` for any ordered field `R` (`R = ℝ` is
`ℂ((t^Γ))`): if `A` has entries of nonnegative valuation, is Hermitian, and its standard part is
positive definite, then `u* A u` is a strictly positive element of `F_Γ = R((t^Γ))` for every
nonzero Hahn vector `u`. Only the real part of the ordinary form of `st A` is assumed positive. -/
theorem leadingVector (A : Matrix n n (Complexify R)⟦Γ⟧) (hA : ∀ i j, 0 ≤ (A i j).orderTop)
    (hH : ∀ i j, conjugation (A i j) = A j i)
    (hst : ∀ x : n → Complexify R, x ≠ 0 →
      0 < (∑ i, ∑ j, star (x i) * (A i j).coeff 0 * x j).re)
    {u : n → (Complexify R)⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : R⟦Γ⟧, 0 < toLex r ∧ hahnHermForm A u = embedRealSeries r := by
  obtain ⟨β, w, x, hx, hscale, h0, hc⟩ :=
    twistedForm_leading conjugationHom _ coeff_conjugationHom A hA hu
  have hfix := twistedForm_map_eq conjugationHom (fun z => by simp) A (fun i j => by simp [hH]) w
  obtain ⟨r, hr, hrw⟩ := exists_embedRealSeries_pos hfix h0
    (by rw [hc]; simpa only [starRingEnd_apply] using hst x hx)
  refine ⟨single (β + β) 1 * r, mul_pos (toLex_single_one_pos _) hr, ?_⟩
  change twistedForm conjugationHom A u = _
  rw [hscale, hrw, map_mul, embedRealSeries_single_one]

/-- `herg:thm:saturation`, general statement in algebraic form: if ordinary conjugate-symmetric
moments `c` have a positive definite Toeplitz matrix `T_N(c)`, then every entrywise
positive-valuation, conjugate-symmetric perturbation `d` keeps `T_N(c + d)` strictly positive
against all Hahn vectors. -/
theorem toeplitz_perturbation_pos (N : ℕ) (c : ℤ → Complexify R) (hc : ∀ k, star (c k) = c (-k))
    (hpd : ∀ x : Fin (N + 1) → Complexify R, x ≠ 0 →
      0 < (∑ j : Fin (N + 1), ∑ k : Fin (N + 1), star (x j) * c ((j : ℤ) - k) * x k).re)
    (d : ℤ → (Complexify R)⟦Γ⟧) (hd : ∀ k, 0 < (d k).orderTop)
    (hds : ∀ k, conjugation (d k) = d (-k)) {u : Fin (N + 1) → (Complexify R)⟦Γ⟧}
    (hu : u ≠ 0) :
    ∃ r : R⟦Γ⟧, 0 < toLex r ∧
      hahnHermForm (toeplitz N fun k => C (c k) + d k) u = embedRealSeries r := by
  refine leadingVector _ (orderTop_toeplitz_nonneg N c d fun k => (hd k).le)
    (toeplitz_hermitian N c d conjugationHom _ coeff_conjugationHom hc (fun k => by simp [hds]))
    (fun x hx => ?_) hu
  simp only [coeff_zero_toeplitz N c d hd]
  exact hpd x hx

/-- The identity Toeplitz matrix `T_N(δ)` is positive definite. -/
theorem re_sum_star_delta_pos {N : ℕ} {x : Fin (N + 1) → Complexify R} (hx : x ≠ 0) :
    0 < (∑ j : Fin (N + 1), ∑ k : Fin (N + 1), star (x j) *
      (if (j : ℤ) - k = 0 then (1 : Complexify R) else 0) * x k).re := by
  have hdiag : ∀ j : Fin (N + 1), ∑ k : Fin (N + 1), star (x j) *
      (if (j : ℤ) - k = 0 then (1 : Complexify R) else 0) * x k = star (x j) * x j := by
    intro j
    rw [sum_eq_single j]
    · simp
    · intro k _ hkj
      have hne : (j : ℤ) - k ≠ 0 := by
        intro h
        exact hkj (Fin.ext (by omega))
      simp [hne]
    · intro h
      exact absurd (mem_univ j) h
  simp only [hdiag, star_mul_self_eq, re_sum]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  refine sum_pos' (fun i _ => ?_) ⟨j, mem_univ j, ?_⟩
  · simpa using Complexify.normSq_nonneg (x i)
  · simpa using Complexify.normSq_pos hj

/-- `herg:thm:saturation`, first statement: for ordinary conjugate-symmetric `b` and a real
infinitesimal `ε`, the moments `c_n = δ_{n0} + ε b_n` have `T_N(c)` strictly positive against all
Hahn vectors, for every `N` and with no growth condition on `b`. The source's normalization
`b_0 = 0` is not needed for positivity. -/
theorem toeplitz_saturation_pos (N : ℕ) (b : ℤ → Complexify R) (hb : ∀ k, b (-k) = star (b k))
    {ε : (Complexify R)⟦Γ⟧} (hε : 0 < ε.orderTop) (hεr : conjugation ε = ε)
    {u : Fin (N + 1) → (Complexify R)⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : R⟦Γ⟧, 0 < toLex r ∧ hahnHermForm
      (toeplitz N fun k => C (if k = 0 then 1 else 0) + ε * C (b k)) u = embedRealSeries r := by
  refine toeplitz_perturbation_pos N (fun k : ℤ => if k = 0 then (1 : Complexify R) else 0)
    (fun k => ?_) (fun x hx => re_sum_star_delta_pos hx) (fun k => ε * C (b k)) (fun k => ?_)
    (fun k => ?_) hu
  · by_cases hk : k = 0 <;> simp [hk]
  · rw [orderTop_mul]
    refine add_pos_of_pos_of_nonneg hε ?_
    rw [C_apply]
    exact orderTop_single_le
  · rw [map_mul, hεr, ← conjugationHom_apply, map_C_of_coeff (conjugationHom (Γ := Γ) (R := R))
      (starRingEnd (Complexify R)) coeff_conjugationHom, starRingEnd_apply, hb]

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem conjugation_single_one (g : Γ) :
    conjugation (single g (1 : Complexify R)) = single g 1 := by
  rw [← embedRealSeries_single_one, conjugation_embedRealSeries]

/-- `herg:thm:saturation`, first statement with `ε = t^η`, `η > 0`. -/
theorem toeplitz_saturation_pos_single (N : ℕ) (b : ℤ → Complexify R)
    (hb : ∀ k, b (-k) = star (b k)) {η : Γ} (hη : 0 < η)
    {u : Fin (N + 1) → (Complexify R)⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : R⟦Γ⟧, 0 < toLex r ∧ hahnHermForm
      (toeplitz N fun k => C (if k = 0 then 1 else 0) + single η 1 * C (b k)) u =
        embedRealSeries r :=
  toeplitz_saturation_pos N b hb (by rw [orderTop_single one_ne_zero]; exact_mod_cast hη)
    (conjugation_single_one η) hu

end Complexify

section Circle

open MeasureTheory

/-- The Fourier moments `c_m = ∫ ζ^{-m} dμ(ζ)` of a measure `μ` on `ℂ`. -/
def circleMoment (μ : Measure ℂ) (m : ℤ) : ℂ := ∫ z, z ^ (-m) ∂μ

variable {μ : Measure ℂ}

theorem integrable_zpow_of_ae_norm_eq_one [IsFiniteMeasure μ] (hT : ∀ᵐ z ∂μ, ‖z‖ = 1)
    (m : ℤ) : Integrable (fun z : ℂ => z ^ m) μ :=
  Integrable.of_bound (measurable_id.pow_const m).aestronglyMeasurable 1
    (hT.mono fun z hz => by simp [norm_zpow, hz])

/-- The moments of a measure on the unit circle are conjugate symmetric. -/
theorem star_circleMoment (hT : ∀ᵐ z ∂μ, ‖z‖ = 1) (m : ℤ) :
    star (circleMoment μ m) = circleMoment μ (-m) := by
  rw [circleMoment, circleMoment, neg_neg, ← starRingEnd_apply, ← integral_conj]
  refine integral_congr_ae (hT.mono fun z hz => ?_)
  simp only
  rw [map_zpow₀, ← Complex.inv_eq_conj hz, inv_zpow', neg_neg]

/-- On the unit circle, `|∑ₖ xₖ ζ^k|² = ∑ⱼ ∑ₖ conj(xⱼ) ζ^{-(j-k)} xₖ`. -/
theorem norm_sq_sum_eq {z : ℂ} (hz : ‖z‖ = 1) {N : ℕ} (x : Fin (N + 1) → ℂ) :
    ((‖∑ k, x k * z ^ (k : ℕ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j : Fin (N + 1), ∑ k : Fin (N + 1), star (x j) * z ^ (-((j : ℤ) - k)) * x k := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sum, sum_mul]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, ← Complex.inv_eq_conj hz, neg_sub, zpow_sub₀ hz0, zpow_natCast,
    zpow_natCast, Complex.star_def, inv_pow, div_eq_mul_inv]
  ring

/-- The Toeplitz form of the moments is the integral of `|∑ₖ xₖ ζ^k|²`. -/
theorem sum_star_circleMoment [IsFiniteMeasure μ] (hT : ∀ᵐ z ∂μ, ‖z‖ = 1) {N : ℕ}
    (x : Fin (N + 1) → ℂ) :
    ∑ j : Fin (N + 1), ∑ k : Fin (N + 1), star (x j) * circleMoment μ ((j : ℤ) - k) * x k =
      ∫ z, ((‖∑ k, x k * z ^ (k : ℕ)‖ ^ 2 : ℝ) : ℂ) ∂μ := by
  have hint : ∀ j k : Fin (N + 1),
      Integrable (fun z : ℂ => star (x j) * z ^ (-((j : ℤ) - k)) * x k) μ := fun j k =>
    ((integrable_zpow_of_ae_norm_eq_one hT _).const_mul _).mul_const _
  rw [integral_congr_ae (hT.mono fun z hz => norm_sq_sum_eq hz x),
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hint j k]
  refine sum_congr rfl fun k _ => ?_
  rw [circleMoment, integral_mul_const, integral_const_mul]

/-- The classical input to `herg:thm:saturation`: the finite Toeplitz forms of an ordinary
positive measure on the unit circle with infinite support are positive definite. A nonzero
polynomial has finitely many zeros, and the measure is not concentrated on them. -/
theorem circleMoment_re_pos [IsFiniteMeasure μ] (hT : ∀ᵐ z ∂μ, ‖z‖ = 1)
    (hsupp : μ.support.Infinite) {N : ℕ} {x : Fin (N + 1) → ℂ} (hx : x ≠ 0) :
    0 < (∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
      star (x j) * circleMoment μ ((j : ℤ) - k) * x k).re := by
  rw [sum_star_circleMoment hT, integral_complex_ofReal, Complex.ofReal_re]
  set P : Polynomial ℂ := ∑ k : Fin (N + 1), Polynomial.C (x k) * Polynomial.X ^ (k : ℕ)
    with hPdef
  have hcoeff : ∀ i : Fin (N + 1), P.coeff i = x i := by
    intro i
    simp [hPdef, Fin.val_inj]
  have hP : P ≠ 0 := by
    intro h
    apply hx
    funext i
    rw [← hcoeff i, h, Polynomial.coeff_zero, Pi.zero_apply]
  have heval : ∀ z, P.eval z = ∑ k, x k * z ^ (k : ℕ) := by
    intro z
    simp [hPdef, Polynomial.eval_finsetSum]
  have hfin : {z : ℂ | ∑ k, x k * z ^ (k : ℕ) = 0}.Finite := by
    simpa [Polynomial.IsRoot, heval] using Polynomial.finite_setOf_isRoot hP
  have hpos : 0 < μ {z : ℂ | ∑ k, x k * z ^ (k : ℕ) = 0}ᶜ := by
    obtain ⟨z₀, hz₀, hz₀'⟩ := (hsupp.sdiff hfin).nonempty
    exact (Measure.mem_support_iff_forall z₀).mp hz₀ _
      (hfin.isClosed.isOpen_compl.mem_nhds hz₀')
  have hint : Integrable (fun z : ℂ => ‖∑ k, x k * z ^ (k : ℕ)‖ ^ 2) μ := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
      ((∑ k, ‖x k‖) ^ 2) (hT.mono fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    gcongr
    calc ‖∑ k, x k * z ^ (k : ℕ)‖ ≤ ∑ k, ‖x k * z ^ (k : ℕ)‖ := norm_sum_le _ _
      _ = ∑ k, ‖x k‖ := by simp [norm_pow, hz]
  have hsupport : Function.support (fun z : ℂ => ‖∑ k, x k * z ^ (k : ℕ)‖ ^ 2) =
      {z : ℂ | ∑ k, x k * z ^ (k : ℕ) = 0}ᶜ := by
    ext z
    simp
  rw [integral_pos_iff_support_of_nonneg (fun z => sq_nonneg _) hint, hsupport]
  exact hpos

open scoped ComplexOrder in
/-- The classical input to `herg:thm:saturation` as a positive definite complex matrix. -/
theorem toeplitz_circleMoment_posDef [IsFiniteMeasure μ] (hT : ∀ᵐ z ∂μ, ‖z‖ = 1)
    (hsupp : μ.support.Infinite) (N : ℕ) : (toeplitz N (circleMoment μ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, toeplitz, star_circleMoment hT, neg_sub]
  · have hform : star x ⬝ᵥ (toeplitz N (circleMoment μ)).mulVec x =
        ∑ j : Fin (N + 1), ∑ k : Fin (N + 1),
          star (x j) * circleMoment μ ((j : ℤ) - k) * x k := by
      simp only [dotProduct, Matrix.mulVec, toeplitz, Matrix.of_apply, Pi.star_apply, mul_sum,
        mul_assoc]
    have hre := circleMoment_re_pos hT hsupp hx
    rw [hform]
    rw [sum_star_circleMoment hT, integral_complex_ofReal] at hre ⊢
    rw [Complex.ofReal_re] at hre
    exact Complex.zero_lt_real.mpr hre

end Circle

section Complex

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {n : Type*} [Fintype n]

/-- Coefficientwise complex conjugation as a ring homomorphism. -/
def complexConjugationHom : ℂ⟦Γ⟧ →+* ℂ⟦Γ⟧ := complexConjugation.toRingHom

@[simp] theorem complexConjugationHom_apply (z : ℂ⟦Γ⟧) :
    complexConjugationHom z = complexConjugation z := rfl

theorem coeff_complexConjugationHom (z : ℂ⟦Γ⟧) (g : Γ) :
    (complexConjugationHom z).coeff g = starRingEnd ℂ (z.coeff g) := rfl

@[simp] theorem complexConjugation_complexConjugation (z : ℂ⟦Γ⟧) :
    complexConjugation (complexConjugation z) = z := by
  apply _root_.HahnSeries.ext
  funext g
  simp

/-- The Hermitian form `u* A u = ∑ᵢ ∑ⱼ conj(uᵢ) Aᵢⱼ uⱼ` over `K_Γ = ℂ((t^Γ))`. -/
def complexHermForm (A : Matrix n n ℂ⟦Γ⟧) (u : n → ℂ⟦Γ⟧) : ℂ⟦Γ⟧ :=
  ∑ i, ∑ j, complexConjugation (u i) * A i j * u j

theorem complexRealEmbedding_single_one (g : Γ) :
    complexRealEmbedding (single g (1 : ℝ)) = single g 1 := by
  apply _root_.HahnSeries.ext
  funext h
  rw [coeff_complexRealEmbedding]
  by_cases hh : h = g
  · subst hh
    rw [coeff_single_same, coeff_single_same, Complex.ofReal_one]
  · rw [coeff_single_of_ne hh, coeff_single_of_ne hh, Complex.ofReal_zero]

/-- A finite conjugation-fixed series whose standard part has positive real part is a positive
element of `F_Γ = ℝ((t^Γ))`. -/
theorem exists_complexRealEmbedding_pos {y : ℂ⟦Γ⟧} (hy : complexConjugation y = y)
    (h0 : 0 ≤ y.orderTop) (hpos : 0 < (y.coeff 0).re) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ y = complexRealEmbedding r := by
  obtain ⟨r, rfl⟩ := (complexConjugation_eq_self_iff_mem_range y).mp hy
  refine ⟨r, pos_of_coeff (i := 0) (fun j hj => ?_) ?_, rfl⟩
  · have h := coeff_eq_zero_of_lt_orderTop (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hj) h0)
    simpa using h
  · simpa using hpos

/-- `herg:lem:leadingvector` over `K_Γ = ℂ((t^Γ))`: if `A ∈ M_n(O_Γ)` is Hermitian and the
ordinary form of `st A` has positive real part at every nonzero `x ∈ ℂⁿ`, then `u* A u` is a
strictly positive element of `F_Γ = ℝ((t^Γ))` for every nonzero `u ∈ K_Γⁿ`. -/
theorem leadingVector_complex (A : Matrix n n ℂ⟦Γ⟧) (hA : ∀ i j, 0 ≤ (A i j).orderTop)
    (hH : ∀ i j, complexConjugation (A i j) = A j i)
    (hst : ∀ x : n → ℂ, x ≠ 0 → 0 < (∑ i, ∑ j, star (x i) * (A i j).coeff 0 * x j).re)
    {u : n → ℂ⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ complexHermForm A u = complexRealEmbedding r := by
  obtain ⟨β, w, x, hx, hscale, h0, hc⟩ :=
    twistedForm_leading complexConjugationHom _ coeff_complexConjugationHom A hA hu
  have hfix := twistedForm_map_eq complexConjugationHom (fun z => by simp) A
    (fun i j => by simp [hH]) w
  obtain ⟨r, hr, hrw⟩ := exists_complexRealEmbedding_pos hfix h0
    (by rw [hc]; simpa only [starRingEnd_apply] using hst x hx)
  refine ⟨single (β + β) 1 * r, mul_pos (toLex_single_one_pos _) hr, ?_⟩
  change twistedForm complexConjugationHom A u = _
  rw [hscale, hrw, map_mul, complexRealEmbedding_single_one]

open scoped ComplexOrder in
/-- `herg:lem:leadingvector` exactly as stated: `A ∈ M_n(O_Γ)` Hermitian with `st A ≻ 0` over
`ℂ` (as a Mathlib positive definite matrix) gives `A ≻ 0` over `K_Γ = ℂ((t^Γ))`. -/
theorem leadingVector_posDef (A : Matrix n n ℂ⟦Γ⟧) (hA : ∀ i j, 0 ≤ (A i j).orderTop)
    (hH : ∀ i j, complexConjugation (A i j) = A j i)
    (hst : (A.map fun a => a.coeff 0).PosDef) {u : n → ℂ⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ complexHermForm A u = complexRealEmbedding r := by
  refine leadingVector_complex A hA hH (fun x hx => ?_) hu
  have h := (Complex.lt_def.mp (hst.dotProduct_mulVec_pos hx)).1
  have hform : star x ⬝ᵥ (A.map fun a => a.coeff 0).mulVec x =
      ∑ i, ∑ j, star (x i) * (A i j).coeff 0 * x j := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, mul_sum, mul_assoc]
  rw [hform, Complex.zero_re] at h
  exact h

/-- `herg:thm:saturation`, general statement in algebraic form over `ℂ((t^Γ))`. -/
theorem complex_toeplitz_perturbation_pos (N : ℕ) (c : ℤ → ℂ) (hc : ∀ k, star (c k) = c (-k))
    (hpd : ∀ x : Fin (N + 1) → ℂ, x ≠ 0 →
      0 < (∑ j : Fin (N + 1), ∑ k : Fin (N + 1), star (x j) * c ((j : ℤ) - k) * x k).re)
    (d : ℤ → ℂ⟦Γ⟧) (hd : ∀ k, 0 < (d k).orderTop)
    (hds : ∀ k, complexConjugation (d k) = d (-k)) {u : Fin (N + 1) → ℂ⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧
      complexHermForm (toeplitz N fun k => C (c k) + d k) u = complexRealEmbedding r := by
  refine leadingVector_complex _ (orderTop_toeplitz_nonneg N c d fun k => (hd k).le)
    (toeplitz_hermitian N c d complexConjugationHom _ coeff_complexConjugationHom hc
      (fun k => by simp [hds])) (fun x hx => ?_) hu
  simp only [coeff_zero_toeplitz N c d hd]
  exact hpd x hx

/-- The identity Toeplitz matrix `T_N(δ)` over `ℂ` is positive definite. -/
theorem complex_re_sum_star_delta_pos {N : ℕ} {x : Fin (N + 1) → ℂ} (hx : x ≠ 0) :
    0 < (∑ j : Fin (N + 1), ∑ k : Fin (N + 1), star (x j) *
      (if (j : ℤ) - k = 0 then (1 : ℂ) else 0) * x k).re := by
  have hdiag : ∀ j : Fin (N + 1), ∑ k : Fin (N + 1), star (x j) *
      (if (j : ℤ) - k = 0 then (1 : ℂ) else 0) * x k = star (x j) * x j := by
    intro j
    rw [sum_eq_single j]
    · simp
    · intro k _ hkj
      have hne : (j : ℤ) - k ≠ 0 := by
        intro h
        exact hkj (Fin.ext (by omega))
      simp [hne]
    · intro h
      exact absurd (mem_univ j) h
  have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  simp only [hdiag, Complex.re_sum, hre]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  exact sum_pos' (fun i _ => sq_nonneg _) ⟨j, mem_univ j, pow_pos (norm_pos_iff.mpr hj) 2⟩

/-- `herg:thm:saturation`, first statement over `ℂ((t^Γ))`, for any real infinitesimal `ε`. The
normalization `b_0 = 0` is not needed for positivity. -/
theorem complex_toeplitz_saturation_pos (N : ℕ) (b : ℤ → ℂ) (hb : ∀ k, b (-k) = star (b k))
    {ε : ℂ⟦Γ⟧} (hε : 0 < ε.orderTop) (hεr : complexConjugation ε = ε)
    {u : Fin (N + 1) → ℂ⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ complexHermForm
      (toeplitz N fun k => C (if k = 0 then 1 else 0) + ε * C (b k)) u =
        complexRealEmbedding r := by
  refine complex_toeplitz_perturbation_pos N (fun k : ℤ => if k = 0 then (1 : ℂ) else 0)
    (fun k => ?_) (fun x hx => complex_re_sum_star_delta_pos hx) (fun k => ε * C (b k))
    (fun k => ?_) (fun k => ?_) hu
  · by_cases hk : k = 0 <;> simp [hk]
  · rw [orderTop_mul]
    refine add_pos_of_pos_of_nonneg hε ?_
    rw [C_apply]
    exact orderTop_single_le
  · rw [map_mul, hεr, ← complexConjugationHom_apply,
      map_C_of_coeff (complexConjugationHom (Γ := Γ)) (starRingEnd ℂ)
        coeff_complexConjugationHom, starRingEnd_apply, hb]

theorem complexConjugation_single_one (g : Γ) :
    complexConjugation (single g (1 : ℂ)) = single g 1 := by
  apply _root_.HahnSeries.ext
  funext h
  by_cases hh : h = g
  · subst hh
    simp
  · simp [coeff_single_of_ne hh]

/-- `herg:thm:saturation`, first statement: with `ε = t^η`, `η > 0`, and ordinary
conjugate-symmetric `b_n ∈ ℂ`, the moments `c_n = δ_{n0} + ε b_n` have `T_N(c) ≻ 0` against all
vectors in `ℂ((t^Γ))^{N+1}`, for every `N`. -/
theorem complex_toeplitz_saturation_pos_single (N : ℕ) (b : ℤ → ℂ)
    (hb : ∀ k, b (-k) = star (b k)) {η : Γ} (hη : 0 < η) {u : Fin (N + 1) → ℂ⟦Γ⟧}
    (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ complexHermForm
      (toeplitz N fun k => C (if k = 0 then 1 else 0) + single η 1 * C (b k)) u =
        complexRealEmbedding r :=
  complex_toeplitz_saturation_pos N b hb (by rw [orderTop_single one_ne_zero]; exact_mod_cast hη)
    (complexConjugation_single_one η) hu

open MeasureTheory in
/-- `herg:thm:saturation`, general statement: the Fourier moments `c_n = ∫ ζ^{-n} dμ` of an
ordinary finite positive measure `μ` on the unit circle with infinite support keep
`T_N(c + d)` strictly positive against all Hahn vectors, for every entrywise positive-valuation
perturbation `d` with `d_{-n} = conj(d_n)`. -/
theorem toeplitz_measure_perturbation_pos (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hT : ∀ᵐ z ∂μ, ‖z‖ = 1) (hsupp : μ.support.Infinite) (N : ℕ) (d : ℤ → ℂ⟦Γ⟧)
    (hd : ∀ k, 0 < (d k).orderTop) (hds : ∀ k, complexConjugation (d k) = d (-k))
    {u : Fin (N + 1) → ℂ⟦Γ⟧} (hu : u ≠ 0) :
    ∃ r : ℝ⟦Γ⟧, 0 < toLex r ∧ complexHermForm
      (toeplitz N fun k => C (circleMoment μ k) + d k) u = complexRealEmbedding r :=
  complex_toeplitz_perturbation_pos N (circleMoment μ) (star_circleMoment hT)
    (fun _ hx => circleMoment_re_pos hT hsupp hx) d hd hds hu

end Complex

end

end Surreal.Herglotz
