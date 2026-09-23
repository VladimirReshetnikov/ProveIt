import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Surreal.HahnSeries.NoncommutativeNeumann

/-!
# Point-spectrum rigidity for coefficientwise Hahn extensions

This file formalizes `ihs:hh:thm:point` (no new normal eigenvalues) and the example
`ihs:hh:ex:backshift` (normality is indispensable) of
`docs/surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex`.

## The extension

For a linear endomorphism `T` of a module `V` over a semiring `k` and exponents in a partially
ordered cancellative commutative monoid `Γ`, `hahnExtend T` is the coefficientwise extension of
`T` to `V((t^Γ)) = HahnModule Γ k V`. It is linear over the Hahn scalars `k((t^Γ))` (the field
`K` of the source when `k = ℂ` and `Γ` is an ordered abelian group), so eigenvalues are taken in
`k((t^Γ))`. For `T` an ordinary bounded operator on a complex Hilbert space `H`, this is the
constant operator `T` of the source acting on `H((t^Γ))`.

## Results

* The eigenspace identity `ker(T - aI) = ker_H(T - aI)((t^Γ))` holds for every endomorphism of a
  module over a commutative ring, without normality: `eigenspace_hahnExtend_C` identifies the
  eigenspace of the extension at the constant `a` with `hahnSubmodule (T.eigenspace a)`, the
  Hahn series all of whose coefficients lie in the ordinary eigenspace, and
  `mem_hahnSubmodule_iff_exists` identifies that submodule with `N((t^Γ))` for
  `N = ker_H(T - aI)`. Consequently `C a` is a Hahn eigenvalue exactly when `a` is an ordinary
  one (`hasEigenvalue_hahnExtend_C_iff`).
* The point-spectrum identity `σ_{p,Γ}(T) = σ_{p,k}(T)`, the ordinary point spectrum embedded
  as constants (the source's `σ_{p,Γ}(T) = σ_{p,ℂ}(T)` when `k = ℂ`), is proved over an
  arbitrary field `k`, for any linearly ordered cancellative commutative monoid `Γ` of exponents
  (in particular every ordered abelian group), under the algebraic hypothesis that
  `ker(T - aI) ∩ Ran(T - aI) = 0` for every scalar `a` (`hasEigenvalue_hahnExtend_iff`,
  `setOf_hasEigenvalue_hahnExtend`). The proof adapts the source's argument. Where the source
  cites `ihs:hh:thm:spectrum` to exclude infinite scalars, a nonzero coefficient of negative
  exponent is excluded directly at the leading exponent. As in the source, the leading
  coefficient `x_δ` is an ordinary eigenvector. Where the source applies the orthogonal
  projection `P` onto `ker(T - aI)`, using `P(T - aI) = 0`, the coefficients at the exponent
  `v(ε) + δ` are compared instead: a nonzero infinitesimal part `ε` would put `x_δ` into
  `Ran(T - aI)`. The identity `P(T - aI) = 0` implies the kernel-range hypothesis, which is all
  this leading-coefficient argument uses.
* For an ordinary bounded normal operator on a complex Hilbert space this hypothesis holds
  (`disjoint_eigenspace_range_of_isStarNormal`), giving `ihs:hh:thm:point` in the source's form
  (`hasEigenvalue_hahnExtend_iff_of_isStarNormal`,
  `setOf_hasEigenvalue_hahnExtend_of_isStarNormal`).
  The final sentence, that the new nonreal spectral points of a self-adjoint operator are not
  eigenvalues, follows from the stronger `not_hasEigenvalue_hahnExtend_of_im_ne_zero`: for
  self-adjoint `T` every Hahn eigenvalue is a real constant
  (`exists_real_of_hasEigenvalue_hahnExtend`), so no scalar of `ℂ((t^Γ))` with a nonreal
  coefficient is an eigenvalue. The source hypothesis `H ≠ 0` is not needed.
* `ihs:hh:ex:backshift`: for any `B` and vectors `e n` with `B e₀ = 0`, `B e_(n+1) = e_n` and
  `e₀ ≠ 0`, the vector `x = ∑ s^n e_n` with `s = t^η`, `η > 0`, satisfies `B x = s x`
  (`hasEigenvector_hahnExtend_shiftEigenvector`), and `s` is not a constant (`single_ne_C`).
  The backward shift `backShift` on `ℓ²(ℕ₀)` is constructed as a bounded operator and the
  example is instantiated with `e_n` the standard basis vectors
  (`backShift_hahnExtend_hasEigenvector`).
  That `B` is not normal is recorded by `not_isStarNormal_backShift`, and
  `not_forall_hasEigenvalue_hahnExtend_backShift` shows that the conclusion of `ihs:hh:thm:point`
  fails for it.

The spectral classification `ihs:hh:thm:spectrum`, which the source proof cites only to exclude
infinite scalars, is not used: that case is handled directly at the leading exponent.
-/

namespace Surreal.InfiniteSpectralPoint

open _root_.HahnSeries

noncomputable section

section Extension

variable {Γ k V : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Semiring k] [AddCommMonoid V] [Module k V]

/-- The coefficientwise extension of a `k`-linear endomorphism `T` of `V` to
`V((t^Γ)) = HahnModule Γ k V`; it is linear over the Hahn scalars `k((t^Γ))`. -/
def hahnExtend (T : Module.End k V) : Module.End k⟦Γ⟧ (HahnModule Γ k V) where
  toFun x := HahnModule.of k (((HahnModule.of k).symm x).map T)
  map_add' x y := by
    ext γ
    simp only [HahnModule.of_symm_add, Equiv.symm_apply_apply, map_coeff, coeff_add, map_add]
  map_smul' c x := by
    ext γ
    have hsub : ((HahnModule.of k).symm
        (HahnModule.of k (((HahnModule.of k).symm x).map T))).support ⊆
        ((HahnModule.of k).symm x).support := by
      intro g hg
      rw [mem_support] at hg ⊢
      intro h
      apply hg
      rw [Equiv.symm_apply_apply, map_coeff, h, map_zero]
    rw [RingHom.id_apply, HahnModule.coeff_smul_right ((HahnModule.of k).symm x).isPWO_support
      hsub, Equiv.symm_apply_apply, map_coeff, HahnModule.coeff_smul, map_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [Equiv.symm_apply_apply, map_coeff, map_smul]

/-- The extension acts coefficientwise: `(T x)_γ = T (x_γ)`. -/
@[simp]
theorem coeff_hahnExtend (T : Module.End k V) (x : HahnModule Γ k V) (γ : Γ) :
    ((HahnModule.of k).symm (hahnExtend (Γ := Γ) T x)).coeff γ =
      T (((HahnModule.of k).symm x).coeff γ) :=
  rfl

/-- The Hahn space `N((t^Γ))` of a subspace `N ⊆ V`, as the `k((t^Γ))`-submodule of `V((t^Γ))`
of the series all of whose coefficients lie in `N`. -/
def hahnSubmodule (N : Submodule k V) : Submodule k⟦Γ⟧ (HahnModule Γ k V) where
  carrier := {x | ∀ γ, ((HahnModule.of k).symm x).coeff γ ∈ N}
  add_mem' {x y} hx hy := by
    intro γ
    rw [HahnModule.of_symm_add, coeff_add]
    exact N.add_mem (hx γ) (hy γ)
  zero_mem' := by
    intro γ
    rw [HahnModule.of_symm_zero, coeff_zero]
    exact N.zero_mem
  smul_mem' c x hx := by
    intro γ
    rw [HahnModule.coeff_smul]
    exact N.sum_mem fun ij _ => N.smul_mem _ (hx ij.2)

/-- A series lies in `hahnSubmodule N` exactly when every coefficient lies in `N`. -/
theorem mem_hahnSubmodule (N : Submodule k V) (x : HahnModule Γ k V) :
    x ∈ hahnSubmodule N ↔ ∀ γ, ((HahnModule.of k).symm x).coeff γ ∈ N :=
  Iff.rfl

/-- `hahnSubmodule N` is the image of `N((t^Γ))` under the coefficientwise inclusion. -/
theorem mem_hahnSubmodule_iff_exists (N : Submodule k V) (x : HahnModule Γ k V) :
    x ∈ hahnSubmodule N ↔
      ∃ y : HahnSeries Γ N, (HahnModule.of k).symm x = y.map N.subtype := by
  constructor
  · intro hx
    refine ⟨⟨fun γ => ⟨((HahnModule.of k).symm x).coeff γ, hx γ⟩,
      ((HahnModule.of k).symm x).isPWO_support.mono fun γ hγ => ?_⟩, ?_⟩
    · intro h
      exact hγ (Subtype.ext h)
    · ext γ
      rfl
  · rintro ⟨y, hy⟩ γ
    rw [hy, map_coeff]
    exact (y.coeff γ).2

end Extension

section CommRing

variable {Γ k V : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing k] [AddCommGroup V] [Module k V]

/-- For a constant scalar `a`, the eigenvalue equation of the extension is coefficientwise. -/
theorem hahnExtend_eq_C_smul_iff (T : Module.End k V) (a : k) (x : HahnModule Γ k V) :
    hahnExtend (Γ := Γ) T x = (C a : k⟦Γ⟧) • x ↔
      ∀ γ, T (((HahnModule.of k).symm x).coeff γ) =
        a • ((HahnModule.of k).symm x).coeff γ := by
  rw [C_apply, HahnModule.single_zero_smul_eq_smul Γ]
  constructor
  · intro h γ
    rw [← coeff_hahnExtend, h, HahnModule.of_symm_smul, HahnSeries.coeff_smul]
  · intro h
    ext γ
    rw [coeff_hahnExtend, h, HahnModule.of_symm_smul, HahnSeries.coeff_smul]

/-- `ihs:hh:thm:point`, eigenspace identity: for every constant `a`,
`ker(T - aI) = ker_H(T - aI)((t^Γ))`. No normality is needed. -/
theorem mem_eigenspace_hahnExtend_C_iff (T : Module.End k V) (a : k) (x : HahnModule Γ k V) :
    x ∈ (hahnExtend T).eigenspace (C a) ↔ x ∈ hahnSubmodule (T.eigenspace a) := by
  rw [Module.End.mem_eigenspace_iff, hahnExtend_eq_C_smul_iff, mem_hahnSubmodule]
  simp only [Module.End.mem_eigenspace_iff]

/-- `ihs:hh:thm:point`, eigenspace identity as an equality of `k((t^Γ))`-submodules. -/
theorem eigenspace_hahnExtend_C (T : Module.End k V) (a : k) :
    (hahnExtend (Γ := Γ) T).eigenspace (C a) = hahnSubmodule (T.eigenspace a) :=
  Submodule.ext (mem_eigenspace_hahnExtend_C_iff T a)

/-- A constant `a` is an eigenvalue of the extension exactly when it is an ordinary eigenvalue;
no normality is needed. -/
theorem hasEigenvalue_hahnExtend_C_iff (T : Module.End k V) (a : k) :
    (hahnExtend (Γ := Γ) T).HasEigenvalue (C a) ↔ T.HasEigenvalue a := by
  constructor
  · intro h
    obtain ⟨x, hxmem, hx⟩ := h.exists_hasEigenvector
    rw [mem_eigenspace_hahnExtend_C_iff, mem_hahnSubmodule] at hxmem
    have hX : (HahnModule.of k).symm x ≠ 0 := hx
    obtain ⟨γ, hγ⟩ : ∃ γ, ((HahnModule.of k).symm x).coeff γ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hX (HahnSeries.ext (funext hall))
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨hxmem γ, hγ⟩
  · intro h
    obtain ⟨v, hvmem, hv⟩ := h.exists_hasEigenvector
    refine Module.End.hasEigenvalue_of_hasEigenvector
      (x := HahnModule.of k (single (0 : Γ) v)) ⟨?_, ?_⟩
    · rw [mem_eigenspace_hahnExtend_C_iff, mem_hahnSubmodule]
      intro γ
      rw [Equiv.symm_apply_apply, coeff_single]
      split_ifs
      · exact hvmem
      · exact Submodule.zero_mem _
    · intro h0
      apply hv
      have h1 := congrArg (fun y : HahnModule Γ k V => ((HahnModule.of k).symm y).coeff 0) h0
      simpa using h1

end CommRing

section Field

variable {Γ k V : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Field k] [AddCommGroup V] [Module k V]

/-- A Hahn eigenvalue has no coefficient at a negative exponent: at the exponent
`v(λ) + v(x) < v(x)` the product `λx` has a nonzero coefficient while that of `T x` vanishes. -/
theorem coeff_eq_zero_of_neg_of_hahnExtend_eq_smul {T : Module.End k V} {μ : k⟦Γ⟧}
    {x : HahnModule Γ k V} (hx : x ≠ 0) (h : hahnExtend (Γ := Γ) T x = μ • x) {γ : Γ}
    (hγ : γ < 0) :
    μ.coeff γ = 0 := by
  by_contra hne
  have hμ : μ ≠ 0 := ne_zero_of_coeff_ne_zero hne
  have hX : (HahnModule.of k).symm x ≠ 0 := hx
  have hord : μ.order < 0 := (order_le_of_coeff_ne_zero hne).trans_lt hγ
  have key := HahnModule.coeff_smul_order_add_order μ x
  rw [← h, coeff_hahnExtend, coeff_eq_zero_of_lt_order (add_lt_of_neg_left _ hord),
    map_zero] at key
  exact smul_ne_zero (leadingCoeff_ne_zero.mpr hμ) (leadingCoeff_ne_zero.mpr hX) key.symm

/-- The infinitesimal part `ε = λ - a`, `a = λ₀`, of a Hahn eigenvalue has no coefficient at a
nonpositive exponent. -/
theorem coeff_sub_C_eq_zero_of_nonpos {T : Module.End k V} {μ : k⟦Γ⟧} {x : HahnModule Γ k V}
    (hx : x ≠ 0) (h : hahnExtend (Γ := Γ) T x = μ • x) {γ : Γ} (hγ : γ ≤ 0) :
    (μ - C (μ.coeff 0)).coeff γ = 0 := by
  rcases hγ.lt_or_eq with hγ | rfl
  · rw [coeff_sub, C_apply, coeff_single_of_ne hγ.ne,
      coeff_eq_zero_of_neg_of_hahnExtend_eq_smul hx h hγ, sub_zero]
  · rw [coeff_sub, C_apply, coeff_single_same, sub_self]

/-- A series `ε` without coefficients at nonpositive exponents contributes nothing to the
coefficient of `ε • x` at the leading exponent of `x`. -/
theorem coeff_smul_order_eq_zero {ε : k⟦Γ⟧} (hε : ∀ γ ≤ 0, ε.coeff γ = 0)
    (x : HahnModule Γ k V) :
    ((HahnModule.of k).symm (ε • x)).coeff ((HahnModule.of k).symm x).order = 0 := by
  by_contra hne
  obtain ⟨α, hα, β, hβ, hsum⟩ := HahnModule.support_smul_subset_vadd_support hne
  have hα0 : 0 < α := lt_of_not_ge fun h => (mem_support _ _).mp hα (hε α h)
  have hβ' : ((HahnModule.of k).symm x).order ≤ β :=
    order_le_of_coeff_ne_zero ((mem_support _ _).mp hβ)
  have hsum' : α + β = ((HahnModule.of k).symm x).order := hsum
  exact (hβ'.trans_lt (lt_add_of_pos_left β hα0)).ne' hsum'

/-- The residual equation `(T - aI) x_γ = (ε x)_γ` for a Hahn eigenvector. -/
theorem hahnExtend_sub_smul_eq {T : Module.End k V} {μ : k⟦Γ⟧} {x : HahnModule Γ k V}
    (h : hahnExtend (Γ := Γ) T x = μ • x) (a : k) (γ : Γ) :
    T (((HahnModule.of k).symm x).coeff γ) - a • ((HahnModule.of k).symm x).coeff γ =
      ((HahnModule.of k).symm ((μ - C a) • x)).coeff γ := by
  rw [sub_smul, ← h, C_apply, HahnModule.single_zero_smul_eq_smul Γ, HahnModule.of_symm_sub,
    coeff_sub, coeff_hahnExtend, HahnModule.of_symm_smul, HahnSeries.coeff_smul]

/-- `ihs:hh:thm:point`, main step: if `ker(T - aI) ∩ Ran(T - aI) = 0` at `a = λ₀`, then a Hahn
eigenvalue `λ` is the constant `a`, and the leading coefficient of any eigenvector is an ordinary
eigenvector for `a`. -/
theorem eq_C_and_hasEigenvector_of_hahnExtend_eq_smul {T : Module.End k V} {μ : k⟦Γ⟧}
    {x : HahnModule Γ k V} (hx : x ≠ 0) (h : hahnExtend (Γ := Γ) T x = μ • x)
    (hT : Disjoint (T.eigenspace (μ.coeff 0)) (LinearMap.range (T - μ.coeff 0 • 1))) :
    μ = C (μ.coeff 0) ∧
      T.HasEigenvector (μ.coeff 0) ((HahnModule.of k).symm x).leadingCoeff := by
  set a := μ.coeff 0 with ha
  set X := (HahnModule.of k).symm x with hXdef
  have hX : X ≠ 0 := hx
  have hε : ∀ γ ≤ 0, (μ - C a).coeff γ = 0 := fun γ hγ =>
    coeff_sub_C_eq_zero_of_nonpos hx h hγ
  have hlead : X.leadingCoeff = X.coeff X.order := leadingCoeff_eq
  have hne : X.coeff X.order ≠ 0 := coeff_order_eq_zero.not.mpr hX
  have heig : T (X.coeff X.order) = a • X.coeff X.order := by
    have h0 := hahnExtend_sub_smul_eq h a X.order
    rw [coeff_smul_order_eq_zero hε x, sub_eq_zero] at h0
    exact h0
  have hmem : X.coeff X.order ∈ T.eigenspace a := Module.End.mem_eigenspace_iff.mpr heig
  refine ⟨?_, ?_⟩
  · by_contra hμ
    have hε0 : μ - C a ≠ 0 := sub_ne_zero.mpr hμ
    have key := hahnExtend_sub_smul_eq h a ((μ - C a).order + X.order)
    rw [HahnModule.coeff_smul_order_add_order, ← hXdef, hlead] at key
    have hran : X.coeff X.order ∈ LinearMap.range (T - a • 1) := by
      refine ⟨((μ - C a).leadingCoeff)⁻¹ • X.coeff ((μ - C a).order + X.order), ?_⟩
      rw [map_smul, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, key,
        smul_smul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hε0), one_smul]
    exact hne (Submodule.disjoint_def.mp hT _ hmem hran)
  · rw [hlead]
    exact ⟨hmem, hne⟩

/-- `ihs:hh:thm:point`, algebraic core: if `ker(T - aI) ∩ Ran(T - aI) = 0` for every scalar
`a`, the eigenvalues of the coefficientwise extension of `T` to `V((t^Γ))` are exactly the
constants `C a` with `a` an ordinary eigenvalue of `T`. -/
theorem hasEigenvalue_hahnExtend_iff (T : Module.End k V)
    (hT : ∀ a : k, Disjoint (T.eigenspace a) (LinearMap.range (T - a • 1))) (μ : k⟦Γ⟧) :
    (hahnExtend (Γ := Γ) T).HasEigenvalue μ ↔ ∃ a, T.HasEigenvalue a ∧ C a = μ := by
  constructor
  · intro hμ
    obtain ⟨x, hxmem, hx⟩ := hμ.exists_hasEigenvector
    obtain ⟨hC, hv⟩ :=
      eq_C_and_hasEigenvector_of_hahnExtend_eq_smul hx
        (Module.End.mem_eigenspace_iff.mp hxmem) (hT _)
    exact ⟨μ.coeff 0, Module.End.hasEigenvalue_of_hasEigenvector hv, hC.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact (hasEigenvalue_hahnExtend_C_iff T a).mpr ha

/-- `ihs:hh:thm:point`, algebraic core, as an identity of point spectra
`σ_{p,Γ}(T) = σ_{p,k}(T)`, the ordinary point spectrum embedded as constants. -/
theorem setOf_hasEigenvalue_hahnExtend (T : Module.End k V)
    (hT : ∀ a : k, Disjoint (T.eigenspace a) (LinearMap.range (T - a • 1))) :
    {μ : k⟦Γ⟧ | (hahnExtend T).HasEigenvalue μ} = C '' {a | T.HasEigenvalue a} := by
  ext μ
  simp only [Set.mem_setOf_eq, Set.mem_image]
  exact hasEigenvalue_hahnExtend_iff T hT μ

end Field

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For an ordinary bounded normal operator, `ker(T - aI) ∩ Ran(T - aI) = 0`: the kernel of the
normal operator `T - aI` is the orthogonal complement of its range. -/
theorem disjoint_eigenspace_range_of_isStarNormal (T : H →L[ℂ] H) [IsStarNormal T] (a : ℂ) :
    Disjoint (Module.End.eigenspace (T : Module.End ℂ H) a)
      (LinearMap.range ((T : Module.End ℂ H) - a • 1)) := by
  have hcomm : Commute T (star (a • (1 : H →L[ℂ] H))) := by
    rw [star_smul, star_one]
    exact (Commute.one_right T).smul_right _
  have hS : IsStarNormal (T - a • (1 : H →L[ℂ] H)) := hcomm.isStarNormal_sub
  have hcoe : ((T - a • (1 : H →L[ℂ] H) : H →L[ℂ] H) : Module.End ℂ H) =
      (T : Module.End ℂ H) - a • 1 := by
    ext v
    simp
  have horth := ContinuousLinearMap.IsStarNormal.orthogonal_range hS
  rw [Module.End.eigenspace_def, ← hcoe]
  rw [← horth]
  exact (Submodule.orthogonal_disjoint _).symm

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- `ihs:hh:thm:point`: for an ordinary bounded normal operator `T` on a complex Hilbert space
`H`, the eigenvalues of its extension to `H((t^Γ))` over `ℂ((t^Γ))` (the source's field `K` when
`Γ` is an ordered abelian group) are exactly the constants `a ∈ σ_{p,ℂ}(T)`. -/
theorem hasEigenvalue_hahnExtend_iff_of_isStarNormal (T : H →L[ℂ] H) [IsStarNormal T]
    (μ : ℂ⟦Γ⟧) :
    (hahnExtend (T : Module.End ℂ H)).HasEigenvalue μ ↔
      ∃ a, Module.End.HasEigenvalue (T : Module.End ℂ H) a ∧ C a = μ :=
  hasEigenvalue_hahnExtend_iff _ (disjoint_eigenspace_range_of_isStarNormal T) μ

/-- `ihs:hh:thm:point`: `σ_{p,Γ}(T) = σ_{p,ℂ}(T)` for an ordinary bounded normal operator. -/
theorem setOf_hasEigenvalue_hahnExtend_of_isStarNormal (T : H →L[ℂ] H) [IsStarNormal T] :
    {μ : ℂ⟦Γ⟧ | (hahnExtend (T : Module.End ℂ H)).HasEigenvalue μ} =
      C '' {a | Module.End.HasEigenvalue (T : Module.End ℂ H) a} :=
  setOf_hasEigenvalue_hahnExtend _ (disjoint_eigenspace_range_of_isStarNormal T)

/-- For an ordinary bounded self-adjoint operator, every eigenvalue of the Hahn extension is a
real constant. -/
theorem exists_real_of_hasEigenvalue_hahnExtend {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {μ : ℂ⟦Γ⟧} (hμ : (hahnExtend (T : Module.End ℂ H)).HasEigenvalue μ) :
    ∃ r : ℝ, Module.End.HasEigenvalue (T : Module.End ℂ H) (r : ℂ) ∧
      C (r : ℂ) = μ := by
  haveI : IsStarNormal T := hT.isStarNormal
  obtain ⟨a, ha, rfl⟩ := (hasEigenvalue_hahnExtend_iff_of_isStarNormal T μ).mp hμ
  have hreal : (starRingEnd ℂ) a = a := hT.isSymmetric.conj_eigenvalue_eq_self ha
  obtain ⟨r, rfl⟩ : ∃ r : ℝ, (r : ℂ) = a := ⟨a.re, Complex.conj_eq_iff_re.mp hreal⟩
  exact ⟨r, ha, rfl⟩

/-- `ihs:hh:thm:point`, final sentence, in a stronger form: for an ordinary bounded self-adjoint
operator, no scalar of `ℂ((t^Γ))` with a nonreal coefficient is an eigenvalue of the Hahn
extension. In particular none of the new nonreal spectral points is an eigenvalue. -/
theorem not_hasEigenvalue_hahnExtend_of_im_ne_zero {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    {μ : ℂ⟦Γ⟧} {γ : Γ} (hγ : (μ.coeff γ).im ≠ 0) :
    ¬ (hahnExtend (T : Module.End ℂ H)).HasEigenvalue μ := by
  intro hμ
  obtain ⟨r, -, rfl⟩ := exists_real_of_hasEigenvalue_hahnExtend hT hμ
  apply hγ
  rw [C_apply, coeff_single]
  split_ifs
  · exact Complex.ofReal_im r
  · exact Complex.zero_im

end Hilbert

section BackShift

open Surreal.InfiniteSpectral

variable {Γ k V : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field k] [AddCommGroup V] [Module k V]

/-- The vector `x = ∑_{n ≥ 0} s^n e_n` of `ihs:hh:ex:backshift`, `s = t^η`, as the strong sum
of the family `n ↦ t^(nη) e_n` (each term is `s^n` times the constant `e_n`, by
`inverseSmoothFamily_apply_eq_smul`). -/
def shiftEigenvector {η : Γ} (hη : 0 < η) (e : ℕ → V) : HahnModule Γ k V :=
  HahnModule.of k (inverseSmoothFamily hη e).hsum

/-- `ihs:hh:ex:backshift`: the coefficient of `x = ∑ s^n e_n` at `nη` is `x_(nη) = e_n`. -/
theorem coeff_shiftEigenvector_nsmul {η : Γ} (hη : 0 < η) (e : ℕ → V) (n : ℕ) :
    ((HahnModule.of k).symm (shiftEigenvector (k := k) hη e)).coeff (n • η) = e n :=
  coeff_hsum_inverseSmoothFamily_nsmul hη e n

/-- `ihs:hh:ex:backshift`: `x = ∑ s^n e_n` has no coefficient off the support `{nη : n ≥ 0}`. -/
theorem coeff_shiftEigenvector_of_notMem {η : Γ} (hη : 0 < η) (e : ℕ → V) {γ : Γ}
    (hγ : γ ∉ Set.range fun n : ℕ => n • η) :
    ((HahnModule.of k).symm (shiftEigenvector (k := k) hη e)).coeff γ = 0 :=
  coeff_hsum_inverseSmoothFamily_of_notMem hη e hγ

/-- `ihs:hh:ex:backshift`: `x = ∑ s^n e_n` is nonzero when `e₀ ≠ 0`, since `x_0 = e₀`. -/
theorem shiftEigenvector_ne_zero {η : Γ} (hη : 0 < η) {e : ℕ → V} (he : e 0 ≠ 0) :
    shiftEigenvector (k := k) hη e ≠ 0 := by
  intro h
  apply he
  have h0 := coeff_shiftEigenvector_nsmul (k := k) hη e 0
  rw [h] at h0
  exact h0.symm

/-- `ihs:hh:ex:backshift`, algebraic form: if `B e₀ = 0` and `B e_(n+1) = e_n`, then
`x = ∑ s^n e_n` satisfies `B x = s x` for `s = t^η`, `η > 0`. -/
theorem hahnExtend_shiftEigenvector (B : Module.End k V) {e : ℕ → V} (h0 : B (e 0) = 0)
    (hs : ∀ n, B (e (n + 1)) = e n) {η : Γ} (hη : 0 < η) :
    hahnExtend (Γ := Γ) B (shiftEigenvector hη e) =
      single η (1 : k) • shiftEigenvector hη e := by
  refine HahnModule.ext _ _ (funext fun γ => ?_)
  rw [coeff_hahnExtend, coeff_single_smul_hahnModule, one_smul]
  by_cases hγ : γ ∈ Set.range fun n : ℕ => n • η
  · obtain ⟨n, rfl⟩ := hγ
    dsimp only
    rcases n with _ | n
    · rw [coeff_shiftEigenvector_nsmul, h0, zero_nsmul, zero_sub,
        coeff_shiftEigenvector_of_notMem hη e (neg_notMem_range_nsmul hη)]
    · rw [coeff_shiftEigenvector_nsmul, hs, succ_nsmul, add_sub_cancel_right,
        coeff_shiftEigenvector_nsmul]
  · rw [coeff_shiftEigenvector_of_notMem hη e hγ, map_zero,
      coeff_shiftEigenvector_of_notMem hη e (sub_notMem_range_nsmul hγ)]

/-- `ihs:hh:ex:backshift`, algebraic form: `x` is an eigenvector of the extension of `B` for the
eigenvalue `s = t^η`. -/
theorem hasEigenvector_hahnExtend_shiftEigenvector (B : Module.End k V) {e : ℕ → V}
    (h0 : B (e 0) = 0) (hs : ∀ n, B (e (n + 1)) = e n) (he : e 0 ≠ 0) {η : Γ} (hη : 0 < η) :
    (hahnExtend B).HasEigenvector (single η (1 : k)) (shiftEigenvector hη e) :=
  ⟨Module.End.mem_eigenspace_iff.mpr (hahnExtend_shiftEigenvector B h0 hs hη),
    shiftEigenvector_ne_zero hη he⟩

/-- The eigenvalue `s = t^η`, `η ≠ 0`, is not a constant. -/
theorem single_ne_C {η : Γ} (hη : η ≠ 0) (a : k) : single η (1 : k) ≠ C a := by
  intro h
  have h1 := congrArg (fun μ : k⟦Γ⟧ => μ.coeff η) h
  simp only [coeff_single_same, C_apply, coeff_single_of_ne hη] at h1
  exact one_ne_zero h1

end BackShift

section L2

open scoped ENNReal lp

/-- The sequences in `ℓ²(ℕ₀)` are closed under the backward shift. -/
theorem memℓp_backShift (f : ℓ²(ℕ, ℂ)) : Memℓp (fun n => f (n + 1)) 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  exact (memℓp_gen_iff hp).mpr
    ((summable_nat_add_iff 1).mpr ((memℓp_gen_iff hp).mp (lp.memℓp f)))

/-- The backward shift on `ℓ²(ℕ₀)` as a linear map. -/
def backShiftLinear : ℓ²(ℕ, ℂ) →ₗ[ℂ] ℓ²(ℕ, ℂ) where
  toFun f := ⟨fun n => f (n + 1), memℓp_backShift f⟩
  map_add' _ _ := lp.ext (funext fun _ => rfl)
  map_smul' _ _ := lp.ext (funext fun _ => rfl)

/-- The backward shift on `ℓ²(ℕ₀)` does not increase the norm. -/
theorem norm_backShiftLinear_le (f : ℓ²(ℕ, ℂ)) : ‖backShiftLinear f‖ ≤ ‖f‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le hp (norm_nonneg f) ?_
  rw [lp.norm_rpow_eq_tsum hp f]
  exact tsum_comp_le_tsum_of_inj ((memℓp_gen_iff hp).mp (lp.memℓp f)) (fun _ => by positivity)
    (add_left_injective 1)

/-- The backward shift `B` on `ℓ²(ℕ₀)`: `B e₀ = 0`, `B e_n = e_(n-1)` for `n ≥ 1`. -/
def backShift : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  backShiftLinear.mkContinuous 1 fun f => by
    rw [one_mul]
    exact norm_backShiftLinear_le f

/-- The backward shift of `ihs:hh:ex:backshift` acts by `(B f)_n = f_(n+1)`. -/
theorem backShift_apply (f : ℓ²(ℕ, ℂ)) (n : ℕ) : backShift f n = f (n + 1) :=
  rfl

/-- The standard basis vector `e_n` of `ℓ²(ℕ₀)`. -/
def basisVec (n : ℕ) : ℓ²(ℕ, ℂ) :=
  lp.single 2 n 1

/-- The `m`-th entry of the standard basis vector `e_n` is `1` if `m = n` and `0` otherwise. -/
theorem basisVec_apply (n m : ℕ) : basisVec n m = if m = n then 1 else 0 := by
  rw [basisVec, lp.single_apply, Pi.single_apply]

/-- The standard basis vector `e_n` of `ℓ²(ℕ₀)` is nonzero. -/
theorem basisVec_ne_zero (n : ℕ) : basisVec n ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : ℓ²(ℕ, ℂ) => f n) h
  simp only [basisVec_apply] at h1
  exact one_ne_zero h1

/-- `ihs:hh:ex:backshift`: `B e₀ = 0`. -/
theorem backShift_basisVec_zero : backShift (basisVec 0) = 0 := by
  refine lp.ext (funext fun m => ?_)
  rw [backShift_apply, basisVec_apply, if_neg (Nat.succ_ne_zero m)]
  rfl

/-- `ihs:hh:ex:backshift`: `B e_(n+1) = e_n`. -/
theorem backShift_basisVec_succ (n : ℕ) : backShift (basisVec (n + 1)) = basisVec n := by
  refine lp.ext (funext fun m => ?_)
  rw [backShift_apply, basisVec_apply, basisVec_apply]
  simp only [Nat.add_right_cancel_iff]

/-- The backward shift is not normal: `e₀ ∈ ker B ∩ Ran B`. -/
theorem not_isStarNormal_backShift : ¬ IsStarNormal backShift := by
  intro hB
  have hd := disjoint_eigenspace_range_of_isStarNormal backShift 0
  have hker : basisVec 0 ∈ Module.End.eigenspace (backShift : Module.End ℂ (ℓ²(ℕ, ℂ))) 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul]
    exact backShift_basisVec_zero
  have hran : basisVec 0 ∈
      LinearMap.range ((backShift : Module.End ℂ (ℓ²(ℕ, ℂ))) - (0 : ℂ) • 1) := by
    refine ⟨basisVec 1, ?_⟩
    rw [zero_smul, sub_zero]
    exact backShift_basisVec_succ 0
  exact basisVec_ne_zero 0 (Submodule.disjoint_def.mp hd _ hker hran)

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- `ihs:hh:ex:backshift`: for the backward shift `B` on `ℓ²(ℕ₀)` and `s = t^η` with
`η > 0`, the vector `x = ∑_{n ≥ 0} s^n e_n` of `ℓ²(ℕ₀)((t^Γ))` is nonzero and satisfies
`B x = s x`, and `s` is not a constant. Its coefficients are `x_(nη) = e_n` and zero off `{nη}`
(`coeff_shiftEigenvector_nsmul`, `coeff_shiftEigenvector_of_notMem`). -/
theorem backShift_hahnExtend_hasEigenvector {η : Γ} (hη : 0 < η) :
    (hahnExtend (backShift : Module.End ℂ (ℓ²(ℕ, ℂ)))).HasEigenvector
        (single η (1 : ℂ)) (shiftEigenvector hη basisVec) ∧
      ∀ a : ℂ, single η (1 : ℂ) ≠ C a :=
  ⟨hasEigenvector_hahnExtend_shiftEigenvector _ backShift_basisVec_zero backShift_basisVec_succ
      (basisVec_ne_zero 0) hη, single_ne_C hη.ne'⟩

/-- `ihs:hh:ex:backshift`: normality is indispensable in `ihs:hh:thm:point`, since for the
nonnormal backward shift the extension has an eigenvalue that is not a constant. -/
theorem not_forall_hasEigenvalue_hahnExtend_backShift {η : Γ} (hη : 0 < η) :
    ¬ ∀ μ : ℂ⟦Γ⟧,
      (hahnExtend (backShift : Module.End ℂ (ℓ²(ℕ, ℂ)))).HasEigenvalue μ → ∃ a : ℂ, C a = μ := by
  intro h
  obtain ⟨hv, hne⟩ := backShift_hahnExtend_hasEigenvector hη
  obtain ⟨a, ha⟩ := h _ (Module.End.hasEigenvalue_of_hasEigenvector hv)
  exact hne a ha.symm

end L2

end

end Surreal.InfiniteSpectralPoint
