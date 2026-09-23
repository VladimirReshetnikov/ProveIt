import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.HahnSeries.Lex
import Mathlib.RingTheory.HahnSeries.Summable
import Surreal.HahnSeries.ComplexNumbers
import Surreal.HahnSeries.CoefficientMapping
import Surreal.HahnSeries.StrongMeasure

/-!
# First nonzero real part and scalar normalization

This file proves `herg:lem:scalar` (clauses (a), (b), (c) and the converse on the halo) and
`herg:cor:scalarnormal` of `docs/surcomplex/hahn-herglotz-positivity/article.tex`.

## The model

A coherent function `f = ∑_γ f_γ t^γ ∈ 𝒪_Γ(U)` (`herg:eq:analyticring`) is a Hahn series
`f : (ℂ → ℂ)⟦Γ⟧` of coefficient functions, all holomorphic on the same set `U`
(`IsCoherentOn`). The coefficients are global functions `ℂ → ℂ`, but only their values on `U`
enter: every hypothesis and conclusion is stated on `U`, and "`f_γ = 0`" means `f_γ = 0` on
`U`. Products are Mathlib's Hahn products, whose coefficients are the finite convolutions of the
source (`IsCoherentOn.mul`). Evaluation at an ordinary point `a` is coefficientwise (`evalAt`)
with values in `K_Γ = ℂ((t^Γ))`. Real and imaginary parts `hahnRe`, `hahnIm` in
`F_Γ = ℝ((t^Γ))` come from the identification `K_Γ = F_Γ[i]` (`realComplexHahnEquiv`), and
`F_Γ` is ordered lexicographically (`toLex`), so `Re f(a) ≥ 0` means `0 ≤ toLex (hahnRe _)`.
The hypothesis `Re f(a) ≥ 0` for every ordinary `a ∈ U` is `HasNonnegReOn`, and "`f` is a
constant in `i F_Γ`" is `IsImagConstOn`: some `c ∈ F_Γ` has `f_γ = i c_γ` on `U` for all `γ`.

The halo `U^# = {a + η : a ∈ U, v(η) > 0}` of `herg:eq:halo` is `hahnHalo U`. The Taylor
evaluation `herg:eq:tayloreval` is `taylorEval f a η = ∑_k D_k η^k`, a strong Hahn sum, with
`D_k = ∑_γ f_γ^{(k)}(a)/k! t^γ` (`taylorCoeff`). Its summability (`taylorFamily`) uses only
the well-ordered support of `f` and the positive valuation of `η`, as in the source; no common
radius of convergence of the coefficients is needed. The source's double family
`(k, γ) ↦ f_γ^{(k)}(a)/k! t^γ η^k` is itself strongly summable (`taylorDoubleFamily`), with
the same sum (`hsum_taylorDoubleFamily`). A halo point `z` is evaluated at `a = st z` and
`η = z - a` (`haloEval`); `haloEval_C_add` identifies this with Taylor evaluation at any
decomposition `z = a + η`. With `η = 0` it is ordinary evaluation (`taylorEval_zero`), and it
depends only on the values of the coefficients on `U` (`taylorEval_congr`, `haloEval_congr`).
At a point of `U`, Taylor evaluation of coherent functions is additive (`taylorEval_sub`), fixes
Hahn constants (`taylorEval_constSeries`), and commutes with multiplication by a Hahn constant
(`taylorEval_mul_constSeries`). `haloEval f z` is meaningful only for `z ∈ hahnHalo U`.

The module does not identify coherent functions with the coherent Hahn sections
`c:p4:def-HU`, `hahnHalo U` with the `K_Γ`-trace of the halo `c:p4:def-halo`, or `taylorEval`
with the coherent evaluation of `c:p4:eval`, all of the analysis report. The source states the
first two identifications in passing and does not cite `c:p4:eval`; none of them is claimed
here.

## Results

* `eqOn_of_re_nonneg_of_re_eq_zero`: the classical strong minimum principle used in the proof,
  for `Re g` with `g` holomorphic on a connected open set, from the open mapping theorem.
* (a) `firstNonzeroRe`: `f` is a constant in `i F_Γ`, or some `γ` has `Re f_β ≡ 0` on `U` for
  `β < γ` and `Re f_γ > 0` on `U`. `re_coeff_pos_of_least` states the second alternative for
  the least exponent with `Re f_γ` not identically zero.
* (b) `isImagConstOn_of_hahnRe_eq_zero`.
* (c) `normalized_of_evalAt_eq_one`.
* Converse: `hahnRe_haloEval_pos`, `Re f(z) > 0` in `F_Γ` for every `z ∈ U^#`. It uses only two
  of the properties in (c), `f_γ = 0` on `U` for `γ < 0` and `Re f_0 > 0` on `U`, and neither
  holomorphy nor any condition on the higher coefficients. `taylorEval_finite` shows that the
  value is finite with standard part `f_0(a)`.
* `herg:cor:scalarnormal`: `scalarNormalization` for `g = scalarNormalize f a₀ =
  (f - i Im f(a₀)) / ρ`: `g` is coherent, `Re g ≥ 0` on `U`, `g(a₀) = 1`, and `g` has the four
  properties of (c). The displayed formula `g(z) = (f(z) - i Im f(a₀)) / ρ` holds at ordinary
  points (`evalAt_scalarNormalize`) and at halo points (`haloEval_scalarNormalize`).
  `scalarNormalize_spec` recovers `f = i Im f(a₀) + g ρ`,
  `scalarNormalization_halo` gives finiteness, a standard part with positive real part, and
  `Re g > 0` on the halo, and `hahnRe_evalAt_pos_of_not_isImagConstOn` shows that `ρ > 0` at
  every ordinary point of `U` unless `f` is a constant in `i F_Γ`.

## Generality

Clauses (a)-(c), the Taylor evaluation and the converse are proved for any linearly ordered
cancellative commutative monoid `Γ`. The corollary divides by `ρ` in the field `F_Γ` and is
proved for any linearly ordered abelian group `Γ`. Neither divisibility nor `Γ ≠ 0` is used,
in line with the source's remark that these results hold for every nonzero `Γ`. The set `U` is
open and connected; Mathlib's `IsConnected` includes nonemptiness, as in the source.

Nothing is pending for `herg:lem:scalar` and `herg:cor:scalarnormal`.
-/

namespace Surreal.HerglotzScalar

open _root_.HahnSeries Surreal.HahnSeries Filter Topology

noncomputable section

section ClassicalMinimum

/-- The classical strong minimum principle for the harmonic function `Re g`: if `g` is
holomorphic on a connected open set, `Re g ≥ 0` there, and `Re g` vanishes at one point, then
`g` is constant. The proof is the open mapping theorem. -/
theorem eqOn_of_re_nonneg_of_re_eq_zero {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hnn : ∀ a ∈ U, 0 ≤ (g a).re) {a₁ : ℂ}
    (ha₁ : a₁ ∈ U) (h0 : (g a₁).re = 0) : ∀ a ∈ U, g a = g a₁ := by
  rcases (hg.analyticOnNhd hU).is_constant_or_isOpen hc.isPreconnected with ⟨w, hw⟩ | hopen
  · intro a ha
    rw [hw a ha, hw a₁ ha₁]
  · exfalso
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp (hopen U subset_rfl hU) (g a₁) ⟨a₁, ha₁, rfl⟩
    have hmem : g a₁ - ((ε / 2 : ℝ) : ℂ) ∈ g '' U := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      exact half_lt_self hε
    obtain ⟨b, hb, hgb⟩ := hmem
    have h := hnn b hb
    rw [hgb, Complex.sub_re, Complex.ofReal_re, h0] at h
    linarith

end ClassicalMinimum

section Coherent

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- Coefficientwise evaluation of a Hahn series of functions at an ordinary point `a`. -/
def evalAt (a : ℂ) : (ℂ → ℂ)⟦Γ⟧ →+* ℂ⟦Γ⟧ :=
  mapCoefficients (Pi.evalRingHom (fun _ : ℂ => ℂ) a)

@[simp] theorem coeff_evalAt (a : ℂ) (f : (ℂ → ℂ)⟦Γ⟧) (γ : Γ) :
    (evalAt a f).coeff γ = f.coeff γ a := rfl

/-- A Hahn constant, viewed as a Hahn series of constant functions. -/
def constSeries : ℂ⟦Γ⟧ →+* (ℂ → ℂ)⟦Γ⟧ :=
  mapCoefficients (Pi.constRingHom ℂ ℂ)

@[simp] theorem coeff_constSeries (c : ℂ⟦Γ⟧) (γ : Γ) (a : ℂ) :
    (constSeries c).coeff γ a = c.coeff γ := rfl

@[simp] theorem evalAt_constSeries (a : ℂ) (c : ℂ⟦Γ⟧) : evalAt a (constSeries c) = c := by
  ext γ
  rfl

/-- The real part in `F_Γ = ℝ((t^Γ))` of an element of `K_Γ = ℂ((t^Γ))`. -/
def hahnRe (z : ℂ⟦Γ⟧) : ℝ⟦Γ⟧ := (realComplexHahnEquiv.symm z).re

/-- The imaginary part in `F_Γ` of an element of `K_Γ`. -/
def hahnIm (z : ℂ⟦Γ⟧) : ℝ⟦Γ⟧ := (realComplexHahnEquiv.symm z).im

@[simp] theorem coeff_hahnRe (z : ℂ⟦Γ⟧) (γ : Γ) : (hahnRe z).coeff γ = (z.coeff γ).re := rfl

@[simp] theorem coeff_hahnIm (z : ℂ⟦Γ⟧) (γ : Γ) : (hahnIm z).coeff γ = (z.coeff γ).im := rfl

/-- `f` is coherent on `U`: every coefficient is holomorphic on the same set `U`. -/
def IsCoherentOn (U : Set ℂ) (f : (ℂ → ℂ)⟦Γ⟧) : Prop :=
  ∀ γ, DifferentiableOn ℂ (f.coeff γ) U

/-- `Re f(a) ≥ 0` in `F_Γ` for every ordinary point `a ∈ U`. -/
def HasNonnegReOn (U : Set ℂ) (f : (ℂ → ℂ)⟦Γ⟧) : Prop :=
  ∀ a ∈ U, 0 ≤ toLex (hahnRe (evalAt a f))

/-- On `U`, `f` is the constant `i c` for some `c ∈ F_Γ`. -/
def IsImagConstOn (U : Set ℂ) (f : (ℂ → ℂ)⟦Γ⟧) : Prop :=
  ∃ c : ℝ⟦Γ⟧, ∀ γ, ∀ a ∈ U, f.coeff γ a = (c.coeff γ : ℂ) * Complex.I

variable {U : Set ℂ} {f : (ℂ → ℂ)⟦Γ⟧}

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem IsCoherentOn.sub {g : (ℂ → ℂ)⟦Γ⟧} (hf : IsCoherentOn U f) (hg : IsCoherentOn U g) :
    IsCoherentOn U (f - g) := fun γ => by
  rw [coeff_sub]
  exact (hf γ).sub (hg γ)

/-- Coherent functions are closed under the finite coefficient convolutions of the product. -/
theorem IsCoherentOn.mul {g : (ℂ → ℂ)⟦Γ⟧} (hf : IsCoherentOn U f) (hg : IsCoherentOn U g) :
    IsCoherentOn U (f * g) := fun γ => by
  rw [coeff_mul]
  exact DifferentiableOn.sum fun ij _ => (hf ij.1).mul (hg ij.2)

theorem isCoherentOn_constSeries (c : ℂ⟦Γ⟧) : IsCoherentOn U (constSeries c) := fun γ =>
  differentiableOn_const (c.coeff γ)

/-- A negative real coefficient below which all real parts vanish would make `Re f(a)`
negative. -/
theorem re_coeff_nonneg_of_forall_lt (hpos : HasNonnegReOn U f) {γ : Γ}
    (hlow : ∀ β < γ, ∀ a ∈ U, (f.coeff β a).re = 0) : ∀ a ∈ U, 0 ≤ (f.coeff γ a).re := by
  intro a ha
  by_contra hneg
  push Not at hneg
  have hlt : toLex (hahnRe (evalAt a f)) < 0 := by
    rw [lt_iff]
    refine ⟨γ, fun j hj => ?_, ?_⟩
    · simp [hlow j hj a ha]
    · simpa using hneg
  exact absurd (hpos a ha) (not_le.mpr hlt)

/-- `herg:lem:scalar`(a), second alternative: the least exponent `γ` at which `Re f_γ` is not
identically zero on `U` has `Re f_γ > 0` everywhere on `U`. -/
theorem re_coeff_pos_of_least (hU : IsOpen U) (hc : IsConnected U) (hf : IsCoherentOn U f)
    (hpos : HasNonnegReOn U f) {γ : Γ} (hlow : ∀ β < γ, ∀ a ∈ U, (f.coeff β a).re = 0)
    (hne : ∃ a ∈ U, (f.coeff γ a).re ≠ 0) : ∀ a ∈ U, 0 < (f.coeff γ a).re := by
  have hnn := re_coeff_nonneg_of_forall_lt hpos hlow
  intro a ha
  refine (hnn a ha).lt_of_ne fun h0 => ?_
  obtain ⟨b, hb, hb0⟩ := hne
  have hconst := eqOn_of_re_nonneg_of_re_eq_zero hU hc (hf γ) hnn ha h0.symm b hb
  exact hb0 (by rw [hconst]; exact h0.symm)

/-- `herg:lem:scalar`(a): either `f` is a constant in `i F_Γ`, or there is an exponent `γ`
such that all earlier real parts vanish identically on `U` and `Re f_γ > 0` on `U`. -/
theorem firstNonzeroRe (hU : IsOpen U) (hc : IsConnected U) (hf : IsCoherentOn U f)
    (hpos : HasNonnegReOn U f) :
    IsImagConstOn U f ∨ ∃ γ, (∀ β < γ, ∀ a ∈ U, (f.coeff β a).re = 0) ∧
      ∀ a ∈ U, 0 < (f.coeff γ a).re := by
  set S : Set Γ := {γ | ∃ a ∈ U, (f.coeff γ a).re ≠ 0} with hSdef
  have hS : S.IsWF := f.isWF_support.subset fun γ ⟨a, _, h⟩ => by
    rw [mem_support]
    intro h0
    apply h
    rw [h0]
    simp
  have hre : ∀ γ, γ ∉ S → ∀ a ∈ U, (f.coeff γ a).re = 0 := fun γ hγ a ha => by
    by_contra hne
    exact hγ ⟨a, ha, hne⟩
  rcases S.eq_empty_or_nonempty with h | h
  · left
    obtain ⟨a₀, ha₀⟩ := hc.nonempty
    have hre0 : ∀ γ, ∀ a ∈ U, (f.coeff γ a).re = 0 := fun γ =>
      hre γ (by rw [h]; exact Set.notMem_empty γ)
    refine ⟨hahnIm (evalAt a₀ f), fun γ a ha => ?_⟩
    rw [eqOn_of_re_nonneg_of_re_eq_zero hU hc (hf γ) (fun b hb => (hre0 γ b hb).ge) ha₀
      (hre0 γ a₀ ha₀) a ha]
    apply Complex.ext <;> simp [hre0 γ a₀ ha₀]
  · right
    refine ⟨hS.min h, fun β hβ => hre β fun hβS => hS.not_lt_min h hβS hβ,
      re_coeff_pos_of_least hU hc hf hpos (fun β hβ => hre β fun hβS => hS.not_lt_min h hβS hβ)
        (hS.min_mem h)⟩

/-- `herg:lem:scalar`(b): if `Re f(a₀) = 0` in `F_Γ` at one ordinary point of `U`, then `f` is
a constant in `i F_Γ`. -/
theorem isImagConstOn_of_hahnRe_eq_zero (hU : IsOpen U) (hc : IsConnected U)
    (hf : IsCoherentOn U f) (hpos : HasNonnegReOn U f) {a₀ : ℂ} (ha₀ : a₀ ∈ U)
    (h : hahnRe (evalAt a₀ f) = 0) : IsImagConstOn U f := by
  rcases firstNonzeroRe hU hc hf hpos with h' | ⟨γ, -, hγ⟩
  · exact h'
  · have h0 := congrArg (fun x : ℝ⟦Γ⟧ => x.coeff γ) h
    simp only [coeff_hahnRe, coeff_evalAt, coeff_zero] at h0
    exact absurd h0 (hγ a₀ ha₀).ne'

/-- `herg:lem:scalar`(c): if `f(a₀) = 1`, then `f_γ = 0` on `U` for `γ < 0`, `f_0(a₀) = 1`,
`Re f_0 > 0` on `U`, and `f_γ(a₀) = 0` for `γ > 0`. -/
theorem normalized_of_evalAt_eq_one (hU : IsOpen U) (hc : IsConnected U)
    (hf : IsCoherentOn U f) (hpos : HasNonnegReOn U f) {a₀ : ℂ} (ha₀ : a₀ ∈ U)
    (h1 : evalAt a₀ f = 1) :
    (∀ γ < 0, ∀ a ∈ U, f.coeff γ a = 0) ∧ f.coeff 0 a₀ = 1 ∧
      (∀ a ∈ U, 0 < (f.coeff 0 a).re) ∧ ∀ γ, 0 < γ → f.coeff γ a₀ = 0 := by
  have h0 : f.coeff 0 a₀ = 1 := by rw [← coeff_evalAt, h1, coeff_one, if_pos rfl]
  have hne : ∀ γ, γ ≠ 0 → f.coeff γ a₀ = 0 := fun γ hγ => by
    rw [← coeff_evalAt, h1, coeff_one, if_neg hγ]
  obtain ⟨γ, hlow, hγ⟩ : ∃ γ, (∀ β < γ, ∀ a ∈ U, (f.coeff β a).re = 0) ∧
      ∀ a ∈ U, 0 < (f.coeff γ a).re := by
    rcases firstNonzeroRe hU hc hf hpos with ⟨c, hc'⟩ | h
    · exfalso
      have h' := congrArg Complex.re (hc' 0 a₀ ha₀)
      simp [h0] at h'
    · exact h
  have hγ0 : γ = 0 := by
    rcases lt_trichotomy γ 0 with h | h | h
    · have h' := hγ a₀ ha₀
      rw [hne γ h.ne] at h'
      simp at h'
    · exact h
    · have h' := hlow 0 h a₀ ha₀
      rw [h0] at h'
      simp at h'
  subst hγ0
  refine ⟨fun β hβ a ha => ?_, h0, hγ, fun β hβ => hne β hβ.ne'⟩
  rw [eqOn_of_re_nonneg_of_re_eq_zero hU hc (hf β) (fun b hb => (hlow β hβ b hb).ge) ha₀
    (hlow β hβ a₀ ha₀) a ha, hne β hβ.ne]

end Coherent

section Halo

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- The `k`-th Taylor coefficient series `D_k = ∑_γ f_γ^{(k)}(a) / k! t^γ` at an ordinary
point `a`. Its support lies in the support of `f`. -/
def taylorCoeff (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) (k : ℕ) : ℂ⟦Γ⟧ where
  coeff γ := iteratedDeriv k (f.coeff γ) a / k.factorial
  isPWO_support' := f.isPWO_support.mono fun γ hγ => by
    rw [mem_support]
    intro h0
    apply hγ
    dsimp only
    rw [h0, iteratedDeriv_const_zero, zero_div]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
@[simp] theorem coeff_taylorCoeff (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) (k : ℕ) (γ : Γ) :
    (taylorCoeff f a k).coeff γ = iteratedDeriv k (f.coeff γ) a / k.factorial := rfl

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem support_taylorCoeff_subset (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) (k : ℕ) :
    (taylorCoeff f a k).support ⊆ f.support := fun γ hγ => by
  rw [mem_support] at hγ ⊢
  intro h0
  apply hγ
  rw [coeff_taylorCoeff, h0, iteratedDeriv_const_zero, zero_div]

/-- The zeroth Taylor coefficient series is ordinary evaluation. -/
@[simp] theorem taylorCoeff_zero (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) : taylorCoeff f a 0 = evalAt a f := by
  ext γ
  simp

/-- The Taylor family `k ↦ D_k η^k` of `herg:eq:tayloreval`. It is strongly summable: the
supports lie in `supp f + ⋃ₖ supp η^k`, and each exponent is reached through the finitely many
pairs of one finite antidiagonal. If `η` is not infinitesimal, `powers` replaces it by `0`. -/
def taylorFamily (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) (η : ℂ⟦Γ⟧) : SummableFamily Γ ℂ ℕ where
  toFun k := taylorCoeff f a k * SummableFamily.powers η k
  isPWO_iUnion_support' := by
    refine (f.isPWO_support.add (SummableFamily.powers η).isPWO_iUnion_support).mono ?_
    refine Set.iUnion_subset fun k => support_mul_subset.trans ?_
    exact Set.add_subset_add (support_taylorCoeff_subset f a k)
      (Set.subset_iUnion (fun k => (SummableFamily.powers η k).support) k)
  finite_co_support' g := by
    classical
    have hS := f.isPWO_support
    have hT := (SummableFamily.powers η).isPWO_iUnion_support
    refine ((Finset.antidiagonal hS hT g).finite_toSet.biUnion fun ij _ =>
      (SummableFamily.powers η).finite_co_support ij.2).subset ?_
    intro k hk
    rw [Set.mem_setOf_eq, coeff_mul] at hk
    obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    rw [Finset.mem_antidiagonal] at hij
    refine Set.mem_biUnion (x := ij) ?_ (right_ne_zero_of_mul hne)
    rw [Finset.mem_coe, Finset.mem_antidiagonal]
    exact ⟨support_taylorCoeff_subset f a k hij.1, Set.mem_iUnion.mpr ⟨k, hij.2.1⟩, hij.2.2⟩

@[simp] theorem taylorFamily_apply (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) (η : ℂ⟦Γ⟧) (k : ℕ) :
    taylorFamily f a η k = taylorCoeff f a k * SummableFamily.powers η k := rfl

/-- Taylor evaluation `f(a + η) = ∑_k D_k η^k` of `herg:eq:tayloreval`, a strong Hahn sum. -/
def taylorEval (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) (η : ℂ⟦Γ⟧) : ℂ⟦Γ⟧ := (taylorFamily f a η).hsum

/-- Taylor evaluation with zero increment is ordinary coefficientwise evaluation. -/
theorem taylorEval_zero (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) : taylorEval f a 0 = evalAt a f := by
  have hpow : ∀ k, SummableFamily.powers (0 : ℂ⟦Γ⟧) k = 0 ^ k := fun k =>
    SummableFamily.powers_of_orderTop_pos (by simp) k
  ext g
  rw [taylorEval, SummableFamily.coeff_hsum, finsum_eq_single _ 0 fun k hk => by
    rw [taylorFamily_apply, hpow, zero_pow hk, mul_zero, coeff_zero]]
  rw [taylorFamily_apply, hpow, pow_zero, mul_one, taylorCoeff_zero]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem mem_support_single {γ x : Γ} {r : ℂ} (hx : x ∈ (single γ r).support) :
    x = γ ∧ r ≠ 0 := by
  rw [mem_support] at hx
  by_cases h : x = γ
  · subst h
    exact ⟨rfl, by rwa [coeff_single_same] at hx⟩
  · exact absurd (coeff_single_of_ne h) hx

/-- The monomials `γ ↦ D_γ t^γ` of a Hahn series form a strongly summable family. -/
def monomialFamily (D : ℂ⟦Γ⟧) : SummableFamily Γ ℂ Γ where
  toFun γ := single γ (D.coeff γ)
  isPWO_iUnion_support' := D.isPWO_support.mono <| Set.iUnion_subset fun γ x hx => by
    obtain ⟨rfl, hr⟩ := mem_support_single hx
    exact (mem_support _ _).mpr hr
  finite_co_support' g := (Set.finite_singleton g).subset fun γ hγ =>
    (mem_support_single ((mem_support _ _).mpr hγ)).1.symm

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
@[simp] theorem monomialFamily_apply (D : ℂ⟦Γ⟧) (γ : Γ) :
    monomialFamily D γ = single γ (D.coeff γ) := rfl

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem hsum_monomialFamily (D : ℂ⟦Γ⟧) : (monomialFamily D).hsum = D := by
  ext g
  rw [SummableFamily.coeff_hsum, finsum_eq_single _ g fun γ hγ => by
    rw [monomialFamily_apply, coeff_single_of_ne (Ne.symm hγ)]]
  rw [monomialFamily_apply, coeff_single_same]

/-- A product coefficient is the finite sum of the contributions of the monomials of the left
factor. -/
theorem coeff_mul_eq_finsum (D P : ℂ⟦Γ⟧) (g : Γ) :
    (D * P).coeff g = ∑ᶠ γ, (single γ (D.coeff γ) * P).coeff g := by
  conv_lhs => rw [mul_comm, ← hsum_monomialFamily D, ← SummableFamily.hsum_smul]
  rw [SummableFamily.coeff_hsum]
  refine finsum_congr fun γ => ?_
  rw [SummableFamily.smul_apply, of_symm_smul_of_eq_mul, mul_comm]
  rfl

/-- The double family `(k, γ) ↦ f_γ^{(k)}(a)/k! t^γ η^k` of `herg:eq:tayloreval`, as written
in the source. It is jointly strongly summable. -/
def taylorDoubleFamily (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) (η : ℂ⟦Γ⟧) : SummableFamily Γ ℂ (ℕ × Γ) where
  toFun p := single p.2 ((taylorCoeff f a p.1).coeff p.2) * SummableFamily.powers η p.1
  isPWO_iUnion_support' := by
    refine (f.isPWO_support.add (SummableFamily.powers η).isPWO_iUnion_support).mono ?_
    refine Set.iUnion_subset fun p => support_mul_subset.trans ?_
    refine Set.add_subset_add (fun x hx => ?_)
      (Set.subset_iUnion (fun k => (SummableFamily.powers η k).support) p.1)
    obtain ⟨rfl, hr⟩ := mem_support_single hx
    exact support_taylorCoeff_subset f a p.1 ((mem_support _ _).mpr hr)
  finite_co_support' g := by
    classical
    have hS := f.isPWO_support
    have hT := (SummableFamily.powers η).isPWO_iUnion_support
    refine ((Finset.antidiagonal hS hT g).finite_toSet.biUnion fun ij _ =>
      ((SummableFamily.powers η).finite_co_support ij.2).prod
        (Set.finite_singleton ij.1)).subset ?_
    intro p hp
    rw [Set.mem_setOf_eq, coeff_mul] at hp
    obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨hij1, hr⟩ := mem_support_single hij.1
    refine Set.mem_biUnion (x := ij) ?_ ⟨right_ne_zero_of_mul hne, hij1.symm⟩
    rw [Finset.mem_coe, Finset.mem_antidiagonal]
    refine ⟨support_taylorCoeff_subset f a p.1 ?_, Set.mem_iUnion.mpr ⟨p.1, hij.2.1⟩, hij.2.2⟩
    rw [hij1]
    exact (mem_support _ _).mpr hr

/-- The strong sum of the double family of `herg:eq:tayloreval` is `taylorEval`, its grouping
by Taylor degree. -/
theorem hsum_taylorDoubleFamily (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) (η : ℂ⟦Γ⟧) :
    (taylorDoubleFamily f a η).hsum = taylorEval f a η := by
  ext g
  rw [SummableFamily.coeff_hsum,
    finsum_curry _ ((taylorDoubleFamily f a η).finite_co_support g), taylorEval,
    SummableFamily.coeff_hsum]
  refine finsum_congr fun k => ?_
  rw [taylorFamily_apply, coeff_mul_eq_finsum]
  rfl

/-- The halo `U^# = {a + η : a ∈ U, η ∈ 𝔪_Γ}` of `herg:eq:halo`. -/
def hahnHalo (U : Set ℂ) : Set ℂ⟦Γ⟧ :=
  {z | ∃ a ∈ U, ∃ η : ℂ⟦Γ⟧, 0 < η.orderTop ∧ C a + η = z}

/-- Evaluation on the halo: `z = a + η` with `a = st z` the coefficient at exponent zero. The
value is meaningful only for `z ∈ hahnHalo U`, and every theorem below assumes this. If
`z - C (z.coeff 0)` is not infinitesimal, `powers` replaces it by `0` and `haloEval f z` is the
junk value `evalAt (z.coeff 0) f`; if `st z ∉ U`, the coefficients are evaluated outside `U`. -/
def haloEval (f : (ℂ → ℂ)⟦Γ⟧) (z : ℂ⟦Γ⟧) : ℂ⟦Γ⟧ := taylorEval f (z.coeff 0) (z - C (z.coeff 0))

/-- The decomposition `z = a + η` of a halo point is unique, so `haloEval` is Taylor
evaluation at `a` with increment `η`. -/
theorem haloEval_C_add (f : (ℂ → ℂ)⟦Γ⟧) (a : ℂ) {η : ℂ⟦Γ⟧} (hη : 0 < η.orderTop) :
    haloEval f (C a + η) = taylorEval f a η := by
  have h0 : (C a + η).coeff 0 = a := by
    rw [coeff_add, C_apply, coeff_single_same,
      coeff_eq_zero_of_lt_orderTop (by exact_mod_cast hη), add_zero]
  rw [haloEval, h0, add_sub_cancel_left]

variable {U : Set ℂ} {f : (ℂ → ℂ)⟦Γ⟧}

theorem orderTop_pow_succ_pos {η : ℂ⟦Γ⟧} (hη : 0 < η.orderTop) (k : ℕ) :
    0 < (η ^ (k + 1)).orderTop := by
  induction k with
  | zero => simpa using hη
  | succ k ih =>
    rw [pow_succ, orderTop_mul]
    exact lt_of_lt_of_le hη (le_add_of_nonneg_left ih.le)

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- Taylor coefficient series at `a ∈ U` depend only on the values of the coefficients on the
open set `U`. -/
theorem taylorCoeff_congr (hU : IsOpen U) {f' : (ℂ → ℂ)⟦Γ⟧}
    (h : ∀ γ, ∀ b ∈ U, f.coeff γ b = f'.coeff γ b) {a : ℂ} (ha : a ∈ U) (k : ℕ) :
    taylorCoeff f a k = taylorCoeff f' a k := by
  ext γ
  have hev : f.coeff γ =ᶠ[𝓝 a] f'.coeff γ := Filter.eventually_of_mem (hU.mem_nhds ha) (h γ)
  rw [coeff_taylorCoeff, coeff_taylorCoeff, hev.iteratedDeriv_eq k]

/-- Taylor evaluation at `a ∈ U` depends only on the values of the coefficients on `U`, so the
model of coherent functions by global coefficient functions is harmless. -/
theorem taylorEval_congr (hU : IsOpen U) {f' : (ℂ → ℂ)⟦Γ⟧}
    (h : ∀ γ, ∀ b ∈ U, f.coeff γ b = f'.coeff γ b) {a : ℂ} (ha : a ∈ U) (η : ℂ⟦Γ⟧) :
    taylorEval f a η = taylorEval f' a η := by
  ext g
  simp only [taylorEval, SummableFamily.coeff_hsum, taylorFamily_apply,
    taylorCoeff_congr hU h ha]

/-- Halo evaluation depends only on the values of the coefficients on `U`. -/
theorem haloEval_congr (hU : IsOpen U) {f' : (ℂ → ℂ)⟦Γ⟧}
    (h : ∀ γ, ∀ b ∈ U, f.coeff γ b = f'.coeff γ b) {z : ℂ⟦Γ⟧} (hz : z ∈ hahnHalo U) :
    haloEval f z = haloEval f' z := by
  obtain ⟨a, ha, η, hη, rfl⟩ := hz
  rw [haloEval_C_add f a hη, haloEval_C_add f' a hη, taylorEval_congr hU h ha]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- The coefficients of a coherent function are smooth at every point of the open set `U`. -/
theorem IsCoherentOn.contDiffAt (hU : IsOpen U) (hf : IsCoherentOn U f) {a : ℂ} (ha : a ∈ U)
    (γ : Γ) (n : ℕ) : ContDiffAt ℂ n (f.coeff γ) a :=
  ((hf γ).contDiffOn hU).contDiffAt (hU.mem_nhds ha)

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- Taylor coefficient series at a point of `U` are additive on coherent functions. -/
theorem taylorCoeff_sub (hU : IsOpen U) {g : (ℂ → ℂ)⟦Γ⟧} (hf : IsCoherentOn U f)
    (hg : IsCoherentOn U g) {a : ℂ} (ha : a ∈ U) (k : ℕ) :
    taylorCoeff (f - g) a k = taylorCoeff f a k - taylorCoeff g a k := by
  ext γ
  rw [coeff_taylorCoeff, coeff_sub, coeff_sub, coeff_taylorCoeff, coeff_taylorCoeff,
    iteratedDeriv_sub (hf.contDiffAt hU ha γ k) (hg.contDiffAt hU ha γ k), sub_div]

/-- Taylor evaluation at a point of `U` is additive on coherent functions. -/
theorem taylorEval_sub (hU : IsOpen U) {g : (ℂ → ℂ)⟦Γ⟧} (hf : IsCoherentOn U f)
    (hg : IsCoherentOn U g) {a : ℂ} (ha : a ∈ U) (η : ℂ⟦Γ⟧) :
    taylorEval (f - g) a η = taylorEval f a η - taylorEval g a η := by
  have h : taylorFamily (f - g) a η = taylorFamily f a η - taylorFamily g a η :=
    SummableFamily.ext fun k => by
      rw [SummableFamily.sub_apply, taylorFamily_apply, taylorFamily_apply, taylorFamily_apply,
        taylorCoeff_sub hU hf hg ha, sub_mul]
  rw [taylorEval, h, SummableFamily.hsum_sub, taylorEval, taylorEval]

/-- A Hahn constant, viewed as a coherent function, has Taylor evaluation equal to itself. -/
theorem taylorEval_constSeries (c : ℂ⟦Γ⟧) (a : ℂ) (η : ℂ⟦Γ⟧) :
    taylorEval (constSeries c) a η = c := by
  ext g
  rw [taylorEval, SummableFamily.coeff_hsum, finsum_eq_single _ 0 fun k hk => ?_]
  · rw [taylorFamily_apply, taylorCoeff_zero, evalAt_constSeries]
    simp
  · have h0 : taylorCoeff (constSeries c) a k = 0 := by
      ext γ
      have hγ : (constSeries c).coeff γ = fun _ => c.coeff γ := rfl
      rw [coeff_taylorCoeff, hγ, iteratedDeriv_const, if_neg hk, zero_div, coeff_zero]
    rw [taylorFamily_apply, h0, zero_mul, coeff_zero]

/-- Taylor evaluation at a point of `U` commutes with subtracting a Hahn constant. -/
theorem taylorEval_sub_constSeries (hU : IsOpen U) (hf : IsCoherentOn U f) {a : ℂ} (ha : a ∈ U)
    (c η : ℂ⟦Γ⟧) : taylorEval (f - constSeries c) a η = taylorEval f a η - c := by
  rw [taylorEval_sub hU hf (isCoherentOn_constSeries c) ha, taylorEval_constSeries]

/-- Taylor coefficient series at a point of `U` commute with multiplication by a Hahn
constant. -/
theorem taylorCoeff_mul_constSeries (hU : IsOpen U) (hf : IsCoherentOn U f) {a : ℂ}
    (ha : a ∈ U) (r : ℂ⟦Γ⟧) (k : ℕ) :
    taylorCoeff (f * constSeries r) a k = taylorCoeff f a k * r := by
  ext γ
  have hsupp : (constSeries r).support ⊆ r.support := fun j hj => by
    rw [mem_support] at hj ⊢
    intro h0
    apply hj
    ext b
    exact h0
  rw [coeff_taylorCoeff, coeff_mul_right' r.isPWO_support hsupp,
    coeff_mul_left' f.isPWO_support (support_taylorCoeff_subset f a k), iteratedDeriv_sum,
    Finset.sum_div]
  · refine Finset.sum_congr rfl fun ij _ => ?_
    have hij : f.coeff ij.1 * (constSeries r).coeff ij.2 = fun x => f.coeff ij.1 x * r.coeff ij.2 :=
      rfl
    rw [hij, iteratedDeriv_mul_const_field, coeff_taylorCoeff, div_mul_eq_mul_div]
  · intro ij _
    exact (hf.contDiffAt hU ha ij.1 k).mul contDiffAt_const

/-- Taylor evaluation at a point of `U` commutes with multiplication by a Hahn constant. -/
theorem taylorEval_mul_constSeries (hU : IsOpen U) (hf : IsCoherentOn U f) {a : ℂ}
    (ha : a ∈ U) (r η : ℂ⟦Γ⟧) : taylorEval (f * constSeries r) a η = taylorEval f a η * r := by
  have h : taylorFamily (f * constSeries r) a η = r • taylorFamily f a η :=
    SummableFamily.ext fun k => by
      rw [SummableFamily.smul_apply, of_symm_smul_of_eq_mul, taylorFamily_apply,
        taylorFamily_apply, taylorCoeff_mul_constSeries hU hf ha]
      ring
  rw [taylorEval, h, SummableFamily.hsum_smul, taylorEval, mul_comm]

omit [IsOrderedCancelAddMonoid Γ] in
/-- If `f_γ = 0` on the open set `U` for `γ < 0`, every Taylor coefficient series at `a ∈ U`
is finite. -/
theorem orderTop_taylorCoeff_nonneg (hU : IsOpen U) (hneg : ∀ γ < 0, ∀ a ∈ U, f.coeff γ a = 0)
    {a : ℂ} (ha : a ∈ U) (k : ℕ) : 0 ≤ (taylorCoeff f a k).orderTop := by
  refine le_orderTop_iff_forall.mpr fun γ hγ => ?_
  have hγ0 : γ < 0 := by exact_mod_cast hγ
  have hev : f.coeff γ =ᶠ[𝓝 a] 0 := Filter.eventually_of_mem (hU.mem_nhds ha) fun b hb => by
    rw [Pi.zero_apply]
    exact hneg γ hγ0 b hb
  rw [coeff_taylorCoeff, hev.iteratedDeriv_eq k, iteratedDeriv_const_zero, zero_div]

/-- At a nonpositive exponent only the zeroth Taylor term contributes. -/
theorem coeff_taylorEval_of_nonpos (hU : IsOpen U)
    (hneg : ∀ γ < 0, ∀ a ∈ U, f.coeff γ a = 0) {a : ℂ} (ha : a ∈ U) {η : ℂ⟦Γ⟧}
    (hη : 0 < η.orderTop) {g : Γ} (hg : g ≤ 0) : (taylorEval f a η).coeff g = f.coeff g a := by
  rw [taylorEval, SummableFamily.coeff_hsum, finsum_eq_single _ 0 fun k hk => ?_]
  · rw [taylorFamily_apply, SummableFamily.powers_of_orderTop_pos hη, pow_zero, mul_one,
      taylorCoeff_zero, coeff_evalAt]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [taylorFamily_apply, SummableFamily.powers_of_orderTop_pos hη]
    apply coeff_eq_zero_of_lt_orderTop
    rw [orderTop_mul]
    refine lt_of_le_of_lt (by exact_mod_cast hg) (lt_of_lt_of_le (orderTop_pow_succ_pos hη k) ?_)
    exact le_add_of_nonneg_left (orderTop_taylorCoeff_nonneg hU hneg ha _)

/-- Proof of the converse of `herg:lem:scalar`: Taylor evaluation at `a + η` is finite, with
standard part `f_0(a)`, when `f_γ = 0` on `U` for `γ < 0`. No condition on the higher
coefficients is used. -/
theorem taylorEval_finite (hU : IsOpen U) (hneg : ∀ γ < 0, ∀ a ∈ U, f.coeff γ a = 0)
    {a : ℂ} (ha : a ∈ U) {η : ℂ⟦Γ⟧} (hη : 0 < η.orderTop) :
    0 ≤ (taylorEval f a η).orderTop ∧ (taylorEval f a η).coeff 0 = f.coeff 0 a := by
  refine ⟨le_orderTop_iff_forall.mpr fun γ hγ => ?_,
    coeff_taylorEval_of_nonpos hU hneg ha hη le_rfl⟩
  have hγ0 : γ < 0 := by exact_mod_cast hγ
  rw [coeff_taylorEval_of_nonpos hU hneg ha hη hγ0.le, hneg γ hγ0 a ha]

/-- The converse clause of `herg:lem:scalar`, at every pair `(a, η)`: if `f_γ = 0` on `U` for
`γ < 0` and `Re f_0 > 0` on `U`, then `Re f(a + η) > 0` in `F_Γ`. -/
theorem hahnRe_taylorEval_pos (hU : IsOpen U) (hneg : ∀ γ < 0, ∀ a ∈ U, f.coeff γ a = 0)
    (h0 : ∀ a ∈ U, 0 < (f.coeff 0 a).re) {a : ℂ} (ha : a ∈ U) {η : ℂ⟦Γ⟧}
    (hη : 0 < η.orderTop) : 0 < toLex (hahnRe (taylorEval f a η)) := by
  refine pos_of_coeff (i := 0) (fun j hj => ?_) ?_
  · rw [coeff_hahnRe, coeff_taylorEval_of_nonpos hU hneg ha hη hj.le, hneg j hj a ha,
      Complex.zero_re]
  · rw [coeff_hahnRe, coeff_taylorEval_of_nonpos hU hneg ha hη le_rfl]
    exact h0 a ha

/-- `herg:lem:scalar`, converse: a function with the properties in (c) has positive real part
on the halo `U^#`. Only `f_γ = 0` on `U` for `γ < 0` and `Re f_0 > 0` on `U` are used. -/
theorem hahnRe_haloEval_pos (hU : IsOpen U) (hneg : ∀ γ < 0, ∀ a ∈ U, f.coeff γ a = 0)
    (h0 : ∀ a ∈ U, 0 < (f.coeff 0 a).re) {z : ℂ⟦Γ⟧} (hz : z ∈ hahnHalo U) :
    0 < toLex (hahnRe (haloEval f z)) := by
  obtain ⟨a, ha, η, hη, rfl⟩ := hz
  rw [haloEval_C_add f a hη]
  exact hahnRe_taylorEval_pos hU hneg h0 ha hη

end Halo

section Normalization

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The imaginary constant `i Im z` of `K_Γ`. -/
def imagConst (z : ℂ⟦Γ⟧) : ℂ⟦Γ⟧ := C Complex.I * complexRealEmbedding (hahnIm z)

@[simp] theorem coeff_imagConst (z : ℂ⟦Γ⟧) (γ : Γ) :
    (imagConst z).coeff γ = Complex.I * ((z.coeff γ).im : ℂ) := by
  rw [imagConst, C_mul_eq_smul, coeff_smul, smul_eq_mul, coeff_complexRealEmbedding,
    coeff_hahnIm]

/-- `z - i Im z` is the embedded real part `Re z`. -/
theorem sub_imagConst (z : ℂ⟦Γ⟧) : z - imagConst z = complexRealEmbedding (hahnRe z) := by
  ext γ
  apply Complex.ext <;> simp

theorem hahnRe_sub_imagConst (z w : ℂ⟦Γ⟧) : hahnRe (z - imagConst w) = hahnRe z := by
  ext γ
  simp

/-- The real part is linear over the real Hahn field `F_Γ`. -/
theorem hahnRe_mul_complexRealEmbedding (w : ℂ⟦Γ⟧) (s : ℝ⟦Γ⟧) :
    hahnRe (w * complexRealEmbedding s) = hahnRe w * s := by
  have hs : realComplexHahnEquiv.symm (complexRealEmbedding s) = ⟨s, 0⟩ := by
    apply QuadraticAlgebra.ext
    · ext γ
      simp
    · ext γ
      simp
  simp only [hahnRe, map_mul, hs, Complexify.mul_re, mul_zero, sub_zero]

/-- The scalar normalization `g = (f - i Im f(a₀)) / ρ`, `ρ = Re f(a₀)`, of
`herg:cor:scalarnormal`. -/
def scalarNormalize (f : (ℂ → ℂ)⟦Γ⟧) (a₀ : ℂ) : (ℂ → ℂ)⟦Γ⟧ :=
  (f - constSeries (imagConst (evalAt a₀ f))) *
    constSeries (complexRealEmbedding (hahnRe (evalAt a₀ f))⁻¹)

variable {U : Set ℂ} {f : (ℂ → ℂ)⟦Γ⟧} {a₀ : ℂ}

/-- The formula `g(a) = (f(a) - i Im f(a₀)) / ρ` of `herg:cor:scalarnormal` at ordinary
points `a`. -/
theorem evalAt_scalarNormalize (a : ℂ) :
    evalAt a (scalarNormalize f a₀) = (evalAt a f - imagConst (evalAt a₀ f)) *
      complexRealEmbedding (hahnRe (evalAt a₀ f))⁻¹ := by
  rw [scalarNormalize, map_mul, map_sub, evalAt_constSeries, evalAt_constSeries]

/-- The formula `g(z) = (f(z) - i Im f(a₀)) / ρ` of `herg:cor:scalarnormal` at halo points
`z ∈ U^#`, with halo evaluation on both sides. -/
theorem haloEval_scalarNormalize (hU : IsOpen U) (hf : IsCoherentOn U f) {z : ℂ⟦Γ⟧}
    (hz : z ∈ hahnHalo U) :
    haloEval (scalarNormalize f a₀) z = (haloEval f z - imagConst (evalAt a₀ f)) *
      complexRealEmbedding (hahnRe (evalAt a₀ f))⁻¹ := by
  obtain ⟨a, ha, η, hη, rfl⟩ := hz
  rw [haloEval_C_add _ a hη, haloEval_C_add f a hη, scalarNormalize,
    taylorEval_mul_constSeries hU (hf.sub (isCoherentOn_constSeries _)) ha,
    taylorEval_sub_constSeries hU hf ha]

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
theorem ne_zero_of_toLex_pos {x : ℝ⟦Γ⟧} (hx : 0 < toLex x) : x ≠ 0 := fun h => by
  rw [h] at hx
  exact lt_irrefl _ hx

/-- Undoing the normalization: `f = i Im f(a₀) + g ρ`, with constant `i Im f(a₀)` and `ρ`. -/
theorem scalarNormalize_spec (hρ : 0 < toLex (hahnRe (evalAt a₀ f))) :
    f = constSeries (imagConst (evalAt a₀ f)) +
      scalarNormalize f a₀ * constSeries (complexRealEmbedding (hahnRe (evalAt a₀ f))) := by
  rw [scalarNormalize, mul_assoc, ← map_mul, ← map_mul,
    inv_mul_cancel₀ (ne_zero_of_toLex_pos hρ), map_one, map_one, mul_one, add_sub_cancel]

theorem isCoherentOn_scalarNormalize (hf : IsCoherentOn U f) :
    IsCoherentOn U (scalarNormalize f a₀) :=
  (hf.sub (isCoherentOn_constSeries _)).mul (isCoherentOn_constSeries _)

/-- Dividing by the positive constant `ρ ∈ F_Γ` preserves `Re ≥ 0`, and subtracting an
imaginary constant does not change the real part. -/
theorem hasNonnegReOn_scalarNormalize (hpos : HasNonnegReOn U f)
    (hρ : 0 < toLex (hahnRe (evalAt a₀ f))) : HasNonnegReOn U (scalarNormalize f a₀) := by
  intro a ha
  rw [evalAt_scalarNormalize, hahnRe_mul_complexRealEmbedding, hahnRe_sub_imagConst]
  change 0 ≤ toLex (hahnRe (evalAt a f)) * (toLex (hahnRe (evalAt a₀ f)))⁻¹
  exact mul_nonneg (hpos a ha) (inv_nonneg.mpr hρ.le)

theorem evalAt_scalarNormalize_self (hρ : 0 < toLex (hahnRe (evalAt a₀ f))) :
    evalAt a₀ (scalarNormalize f a₀) = 1 := by
  rw [evalAt_scalarNormalize, sub_imagConst, ← map_mul,
    mul_inv_cancel₀ (ne_zero_of_toLex_pos hρ), map_one]

/-- `herg:cor:scalarnormal`: if `Re f(a₀) = ρ > 0`, then `g = (f - i Im f(a₀)) / ρ` is
coherent, has `Re g ≥ 0` at ordinary points of `U`, satisfies `g(a₀) = 1`, and has exactly the
form of `herg:lem:scalar`(c): `g_γ = 0` on `U` for `γ < 0`, `g_0(a₀) = 1`, `Re g_0 > 0` on `U`,
and `g_γ(a₀) = 0` for `γ > 0`. -/
theorem scalarNormalization (hU : IsOpen U) (hc : IsConnected U) (hf : IsCoherentOn U f)
    (hpos : HasNonnegReOn U f) (ha₀ : a₀ ∈ U) (hρ : 0 < toLex (hahnRe (evalAt a₀ f))) :
    IsCoherentOn U (scalarNormalize f a₀) ∧ HasNonnegReOn U (scalarNormalize f a₀) ∧
      evalAt a₀ (scalarNormalize f a₀) = 1 ∧
      (∀ γ < 0, ∀ a ∈ U, (scalarNormalize f a₀).coeff γ a = 0) ∧
      (scalarNormalize f a₀).coeff 0 a₀ = 1 ∧
      (∀ a ∈ U, 0 < ((scalarNormalize f a₀).coeff 0 a).re) ∧
      ∀ γ, 0 < γ → (scalarNormalize f a₀).coeff γ a₀ = 0 :=
  ⟨isCoherentOn_scalarNormalize hf, hasNonnegReOn_scalarNormalize hpos hρ,
    evalAt_scalarNormalize_self hρ,
    normalized_of_evalAt_eq_one hU hc (isCoherentOn_scalarNormalize hf)
      (hasNonnegReOn_scalarNormalize hpos hρ) ha₀ (evalAt_scalarNormalize_self hρ)⟩

/-- The last sentence of `herg:cor:scalarnormal`: on the halo `U^#` the normalized function `g`
is finite, its standard part has strictly positive real part, and `Re g > 0` in `F_Γ`. -/
theorem scalarNormalization_halo (hU : IsOpen U) (hc : IsConnected U) (hf : IsCoherentOn U f)
    (hpos : HasNonnegReOn U f) (ha₀ : a₀ ∈ U) (hρ : 0 < toLex (hahnRe (evalAt a₀ f)))
    {z : ℂ⟦Γ⟧} (hz : z ∈ hahnHalo U) :
    0 ≤ (haloEval (scalarNormalize f a₀) z).orderTop ∧
      0 < ((haloEval (scalarNormalize f a₀) z).coeff 0).re ∧
      0 < toLex (hahnRe (haloEval (scalarNormalize f a₀) z)) := by
  obtain ⟨-, -, -, hneg, -, h0, -⟩ := scalarNormalization hU hc hf hpos ha₀ hρ
  obtain ⟨a, ha, η, hη, rfl⟩ := hz
  obtain ⟨hfin, hst⟩ := taylorEval_finite hU hneg ha hη
  rw [haloEval_C_add _ a hη]
  exact ⟨hfin, hst ▸ h0 a ha, hahnRe_taylorEval_pos hU hneg h0 ha hη⟩

/-- `herg:cor:scalarnormal`, final sentence: a function with `Re ≥ 0` on `U` that is not a
constant in `i F_Γ` has `ρ = Re f(a₀) > 0` at every ordinary `a₀ ∈ U`, so it normalizes. -/
theorem hahnRe_evalAt_pos_of_not_isImagConstOn (hU : IsOpen U) (hc : IsConnected U)
    (hf : IsCoherentOn U f) (hpos : HasNonnegReOn U f) (hnc : ¬ IsImagConstOn U f)
    (ha₀ : a₀ ∈ U) : 0 < toLex (hahnRe (evalAt a₀ f)) :=
  (hpos a₀ ha₀).lt_of_ne fun h =>
    hnc (isImagConstOn_of_hahnRe_eq_zero hU hc hf hpos ha₀ (by simpa using h.symm))

end Normalization

end

end Surreal.HerglotzScalar
