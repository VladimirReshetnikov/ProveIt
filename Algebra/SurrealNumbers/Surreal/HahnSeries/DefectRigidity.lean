import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Projection
import Surreal.HahnSeries.ContinuumDefects
import Surreal.HahnSeries.NoncommutativeNeumann
import Surreal.HahnSeries.PointSpectrumRigidity
import Surreal.HahnSeries.RowColumnFinite

/-!
# Positive-order defect rigidity

This file formalizes `ihs:hh:thm:defect` (positive-order defect rigidity, with
`ihs:hh:eq:defectdecomp`), its corollaries `ihs:hh:cor:norepair` and `ihs:hh:cor:independent`,
and `ihs:hh:thm:continuum` of
`docs/surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex`.

## Setting

The source's complex vector space `V` is a module over a commutative ring `k`; a field is needed
only for the dimension bound of `ihs:hh:cor:independent`. The exponents form a linearly ordered
cancellative commutative monoid `Γ`, so every linearly ordered abelian group is covered; the
source's assumption `Γ ≠ 0` is not used. The space `V_Γ = V((t^Γ))` is `HahnModule Γ k V`, a
module over `K = k((t^Γ))`. An operator series `E ∈ End_k(V)((t^Γ))` acts on `V_Γ` by the
convolution `(E x)_γ = ∑_{α + β = γ} E_α x_β` (`opAct`): Mathlib's action of `End_k(V)((t^Γ))` on
`HahnModule Γ (End_k V) V` is transported along the identity of the underlying Hahn series. It is
`K`-linear because scalar series are central (`hahnMap_mul_comm`), `opActHom` is a ring
homomorphism into `End_K(V_Γ)`, and constants act coefficientwise
(`opAct_C : opAct (C T) = hahnExtend T`). The operator `A = S + E` is
`perturbOp S E = opAct (C S + E)`. "Strictly positive order, or zero" is `0 < E.orderTop`. No
commutation of `E` with `S` is assumed.

## Results

* `ihs:hh:thm:defect`, for injective `S`. At any exponent `γ` below which `x` vanishes, the
  coefficient of `Ax` is `S x_γ` (`coeff_perturbOp`), so `Ax` and `x` vanish below the same
  thresholds (`forall_lt_coeff_perturbOp_eq_zero_iff`). Hence `v(Ax) = v(x)`
  (`orderTop_perturbOp`, for all `x`, both sides being `⊤` at `0`), the leading coefficient of
  `Ax` is `S x_{v(x)}` (`leadingCoeff_perturbOp`), and `A` is injective (`injective_perturbOp`).
  These hold without a complement, and the valuation statements also hold over a commutative
  semiring. Given an algebraic complement `V = Ran S ⊕ W`, the source's proof is followed:
  `U(Sv + w) = v` (`leftInv`, with `US = I`, `leftInv_mul`, and `ker U = W`), the Neumann inverse
  `R = (I + UE)⁻¹ = ∑ (-UE)^n` of `ihs:lem:neumann` in the noncommutative algebra
  `End_k(V)((t^Γ))`, `L = RU` (`defectLeftInv`) and `Π = I - AL` (`defectProj`). The identities
  `LA = I` (`defectLeftInv_mul`) and `UΠ = 0` (`C_leftInv_mul_defectProj`) give that `Π` kills
  `Ran A` (`defectProj_perturbOp`), takes values in `W((t^Γ))` (`defectProj_mem`) and is the
  identity there (`defectProj_of_mem`). Here `W((t^Γ))` is `hahnSubmodule W`, the series with all
  coefficients in `W`. Hence `V_Γ = A(V_Γ) ⊕ W((t^Γ))` (`isCompl_range_perturbOp`) and
  `coker A ≅ hahnSubmodule W` as `K`-modules (`cokernelEquiv`). The coefficientwise inclusion
  `hahnInclusion` identifies the Hahn module `HahnModule Γ k W` with `hahnSubmodule W`
  (`hahnSubmoduleEquiv`), so also `coker A ≅ HahnModule Γ k W` (`cokernelEquivHahnModule`).
* `ihs:hh:cor:norepair`: `not_surjective_perturbOp`. More precisely, a constant `f ∉ Ran S` stays
  outside `Ran A` (`single_notMem_range_perturbOp`), so no complement is needed.
* `ihs:hh:cor:independent`: `linearIndependent_mkQ_single`, by the source's least-exponent
  argument, for an arbitrary index type. For a field `k`, the bound
  `dim_K coker(S + E) ≥ dim_k (V / Ran S)` is `lift_rank_quotient_le_rank_coker`, with the
  two cardinals lifted to a common universe.
* `ihs:hh:thm:continuum`: take `H = ℓ²` and `D e_n = n⁻¹ e_n`. `D` is `invDiag` on `ℓ²(ℕ, ℂ)`,
  the source's `ℓ²(ℕ_{≥1})` in the shifted indexing of `Surreal.HahnSeries.ContinuumDefects`.
  Combining `ihs:hh:cor:independent` with `ihs:hh:lem:continuum` (`linearIndependent_powerVec_mkQ`
  and its `D²` form `linearIndependent_powerVec_mkQ_sq`) gives `2^ℵ₀ ≤ dim_K coker(D + E)` and
  `2^ℵ₀ ≤ dim_K coker(D² + E)` for every `E ∈ B(H)((t^Γ))` of positive order, zero included
  (`continuum_le_rank_coker`). Such an `E` acts through the coefficientwise inclusion
  `B(H) → End_ℂ(H)`. The same bounds hold for every `E ∈ End_ℂ(H)((t^Γ))` of positive order
  (`continuum_le_rank_coker_invDiag`, `continuum_le_rank_coker_invDiag_sq`).

## Not formalized

The source's closing remark that the isomorphism `coker A ≅ W((t^Γ))` depends on the chosen
complement is informal and is not formalized, beyond the complement-free statements
`ihs:hh:cor:norepair` and `ihs:hh:cor:independent`. The warning `ihs:hh:warn:dimension` is not
formalized.
-/

namespace Surreal.DefectRigidity

open _root_.HahnSeries
open Surreal.InfiniteSpectral Surreal.InfiniteSpectralPoint Surreal.RowColumnFinite

noncomputable section

section Action

variable {Γ k V : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommSemiring k] [AddCommMonoid V] [Module k V]

theorem support_hahnMap_subset (c : k⟦Γ⟧) :
    (hahnMap k (Module.End k V) c).support ⊆ c.support := by
  intro g hg
  rw [HahnSeries.mem_support] at hg ⊢
  contrapose hg
  rw [coeff_hahnMap, hg, map_zero]

/-- Scalar series act on `V((t^Γ))` through scalar operators: over `End_k(V)`, the series
`hahnMap c` acts as `c ∈ k((t^Γ))` does on the `k((t^Γ))`-module `V((t^Γ))`. -/
theorem of_hahnMap_smul (c : k⟦Γ⟧) (y : HahnModule Γ (Module.End k V) V) :
    HahnModule.of k ((HahnModule.of (Module.End k V)).symm (hahnMap k (Module.End k V) c • y)) =
      c • HahnModule.of k ((HahnModule.of (Module.End k V)).symm y) := by
  refine HahnModule.ext _ _ (funext fun g => ?_)
  rw [Equiv.symm_apply_apply, HahnModule.coeff_smul_left (x := hahnMap k (Module.End k V) c)
    c.isPWO_support (support_hahnMap_subset c), HahnModule.coeff_smul]
  rfl

theorem of_smul_eq_hahnMap_smul (c : k⟦Γ⟧) (x : HahnModule Γ k V) :
    HahnModule.of (Module.End k V) ((HahnModule.of k).symm (c • x)) =
      hahnMap k (Module.End k V) c •
        HahnModule.of (Module.End k V) ((HahnModule.of k).symm x) := by
  have h := of_hahnMap_smul c (HahnModule.of (Module.End k V) ((HahnModule.of k).symm x))
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

section Smul

variable (E F : (Module.End k V)⟦Γ⟧) (y : HahnModule Γ (Module.End k V) V)

theorem end_mul_smul : (E * F) • y = E • F • y :=
  mul_smul E F y

theorem end_one_smul : (1 : (Module.End k V)⟦Γ⟧) • y = y :=
  one_smul _ y

theorem end_zero_smul : (0 : (Module.End k V)⟦Γ⟧) • y = 0 :=
  HahnModule.zero_smul'

theorem end_add_smul : (E + F) • y = E • y + F • y :=
  add_smul E F y

end Smul

/-- The convolution action `(E x)_γ = ∑_{α + β = γ} E_α x_β` of an operator-valued Hahn series
`E ∈ End_k(V)((t^Γ))` on `V((t^Γ))`, as a `k((t^Γ))`-linear map. -/
def opAct (E : (Module.End k V)⟦Γ⟧) : Module.End k⟦Γ⟧ (HahnModule Γ k V) where
  toFun x := HahnModule.of k ((HahnModule.of (Module.End k V)).symm
    (E • HahnModule.of (Module.End k V) ((HahnModule.of k).symm x)))
  map_add' x y := by
    rw [HahnModule.of_symm_add, HahnModule.of_add, smul_add, HahnModule.of_symm_add,
      HahnModule.of_add]
  map_smul' c x := by
    rw [RingHom.id_apply, of_smul_eq_hahnMap_smul, ← end_mul_smul, ← hahnMap_mul_comm,
      end_mul_smul, of_hahnMap_smul]

theorem opAct_apply (E : (Module.End k V)⟦Γ⟧) (x : HahnModule Γ k V) :
    opAct E x = HahnModule.of k ((HahnModule.of (Module.End k V)).symm
      (E • HahnModule.of (Module.End k V) ((HahnModule.of k).symm x))) :=
  rfl

/-- The convolution action as a ring homomorphism
`End_k(V)((t^Γ)) → End_{k((t^Γ))}(V((t^Γ)))`. -/
def opActHom : (Module.End k V)⟦Γ⟧ →+* Module.End k⟦Γ⟧ (HahnModule Γ k V) where
  toFun := opAct
  map_one' := LinearMap.ext fun x => by
    rw [opAct_apply, end_one_smul, Equiv.symm_apply_apply, Equiv.apply_symm_apply,
      Module.End.one_apply]
  map_mul' E F := LinearMap.ext fun x => by
    rw [Module.End.mul_apply, opAct_apply, opAct_apply, opAct_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply, end_mul_smul]
  map_zero' := LinearMap.ext fun x => by
    rw [opAct_apply, end_zero_smul, LinearMap.zero_apply]
    rfl
  map_add' E F := LinearMap.ext fun x => by
    rw [LinearMap.add_apply, opAct_apply, opAct_apply, opAct_apply, end_add_smul]
    rfl

theorem opAct_one : opAct (1 : (Module.End k V)⟦Γ⟧) = (1 : Module.End k⟦Γ⟧ (HahnModule Γ k V)) :=
  map_one opActHom

theorem opAct_zero : opAct (0 : (Module.End k V)⟦Γ⟧) = (0 : Module.End k⟦Γ⟧ (HahnModule Γ k V)) :=
  map_zero opActHom

theorem opAct_mul (E F : (Module.End k V)⟦Γ⟧) : opAct (E * F) = opAct E * opAct F :=
  map_mul opActHom E F

theorem opAct_add (E F : (Module.End k V)⟦Γ⟧) : opAct (E + F) = opAct E + opAct F :=
  map_add opActHom E F

theorem coeff_opAct (E : (Module.End k V)⟦Γ⟧) (x : HahnModule Γ k V) (γ : Γ) :
    ((HahnModule.of k).symm (opAct E x)).coeff γ =
      ((HahnModule.of (Module.End k V)).symm
        (E • HahnModule.of (Module.End k V) ((HahnModule.of k).symm x))).coeff γ :=
  rfl

/-- A constant operator `T` acts coefficientwise. -/
theorem coeff_opAct_C (T : Module.End k V) (x : HahnModule Γ k V) (γ : Γ) :
    ((HahnModule.of k).symm (opAct (Γ := Γ) (C T) x)).coeff γ =
      T (((HahnModule.of k).symm x).coeff γ) := by
  rw [coeff_opAct, C_apply, HahnModule.single_zero_smul_eq_smul Γ, HahnModule.of_symm_smul,
    HahnSeries.coeff_smul, Equiv.symm_apply_apply, Module.End.smul_def]

/-- On constants the convolution action is the coefficientwise extension `hahnExtend`. -/
theorem opAct_C (T : Module.End k V) : opAct (Γ := Γ) (C T) = hahnExtend T :=
  LinearMap.ext fun x => HahnModule.ext _ _ (funext fun γ =>
    (coeff_opAct_C T x γ).trans (coeff_hahnExtend T x γ).symm)

/-- The operator `A = S + E` on `V((t^Γ))`: the coefficientwise extension of `S` plus the
convolution action of `E`. -/
def perturbOp (S : Module.End k V) (E : (Module.End k V)⟦Γ⟧) :
    Module.End k⟦Γ⟧ (HahnModule Γ k V) :=
  opAct (C S + E)

theorem perturbOp_def (S : Module.End k V) (E : (Module.End k V)⟦Γ⟧) :
    perturbOp S E = opAct (C S + E) :=
  rfl

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem of_symm_sum {ι : Type*} (s : Finset ι) (z : ι → HahnModule Γ k V) :
    (HahnModule.of k).symm (∑ i ∈ s, z i) = ∑ i ∈ s, (HahnModule.of k).symm (z i) :=
  Finset.cons_induction rfl (fun i s his h => by
    rw [Finset.sum_cons, Finset.sum_cons, HahnModule.of_symm_add, h]) s

/-- The coefficientwise inclusion `W((t^Γ)) → V((t^Γ))` induced by a subspace `W ⊆ V`, where
`W((t^Γ))` is the Hahn module `HahnModule Γ k W`; it is `k((t^Γ))`-linear. -/
def hahnInclusion (W : Submodule k V) : HahnModule Γ k W →ₗ[k⟦Γ⟧] HahnModule Γ k V where
  toFun y := HahnModule.of k (((HahnModule.of k).symm y).map W.subtype)
  map_add' x y := by
    ext γ
    simp only [HahnModule.of_symm_add, Equiv.symm_apply_apply, map_coeff, coeff_add, map_add]
  map_smul' c x := by
    ext γ
    have hsub : ((HahnModule.of k).symm
        (HahnModule.of k (((HahnModule.of k).symm x).map W.subtype))).support ⊆
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

/-- The inclusion `W((t^Γ)) → V((t^Γ))` acts coefficientwise. -/
theorem coeff_hahnInclusion (W : Submodule k V) (y : HahnModule Γ k W) (γ : Γ) :
    ((HahnModule.of k).symm (hahnInclusion (Γ := Γ) W y)).coeff γ =
      (((HahnModule.of k).symm y).coeff γ : V) :=
  rfl

theorem injective_hahnInclusion (W : Submodule k V) :
    Function.Injective (hahnInclusion (Γ := Γ) W) := fun _ _ h =>
  HahnModule.ext _ _ (funext fun γ =>
    Subtype.ext (congrArg (fun x => ((HahnModule.of k).symm x).coeff γ) h))

/-- The image of `W((t^Γ))` in `V((t^Γ))` is `hahnSubmodule W`. -/
theorem range_hahnInclusion (W : Submodule k V) :
    LinearMap.range (hahnInclusion (Γ := Γ) W) = hahnSubmodule W := by
  ext x
  rw [LinearMap.mem_range, mem_hahnSubmodule_iff_exists]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(HahnModule.of k).symm y, rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨HahnModule.of k y, HahnModule.ext _ _ (funext fun γ => ?_)⟩
    rw [hy]
    rfl

/-- The Hahn module `W((t^Γ)) = HahnModule Γ k W` is isomorphic, as a `k((t^Γ))`-module, to the
submodule `hahnSubmodule W` of `V((t^Γ))`, through the coefficientwise inclusion. -/
def hahnSubmoduleEquiv (W : Submodule k V) :
    HahnModule Γ k W ≃ₗ[k⟦Γ⟧] hahnSubmodule (Γ := Γ) W :=
  (LinearEquiv.ofInjective _ (injective_hahnInclusion W)).trans
    (LinearEquiv.ofEq _ _ (range_hahnInclusion W))

theorem coe_hahnSubmoduleEquiv_apply (W : Submodule k V) (y : HahnModule Γ k W) :
    (hahnSubmoduleEquiv (Γ := Γ) W y : HahnModule Γ k V) = hahnInclusion (Γ := Γ) W y :=
  rfl

end Action

section Order

variable {Γ k V : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommSemiring k] [AddCommMonoid V] [Module k V]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- Every exponent in the support of a series of positive order is positive. -/
theorem pos_of_coeff_ne_zero {R : Type*} [Zero R] [Zero Γ] {E : R⟦Γ⟧} (hE : 0 < E.orderTop)
    {α : Γ} (hα : E.coeff α ≠ 0) : 0 < α :=
  WithTop.coe_pos.mp (hE.trans_le (orderTop_le_of_coeff_ne_zero hα))

/-- A positive-order perturbation does not reach an exponent `γ` below which `x` vanishes:
`(E x)_γ = ∑_{α + β = γ} E_α x_β = 0`, since `α > 0` forces `β < γ`. -/
theorem coeff_opAct_eq_zero {E : (Module.End k V)⟦Γ⟧} (hE : 0 < E.orderTop)
    {x : HahnModule Γ k V} {γ : Γ} (hx : ∀ β < γ, ((HahnModule.of k).symm x).coeff β = 0) :
    ((HahnModule.of k).symm (opAct E x)).coeff γ = 0 := by
  by_contra hne
  rw [coeff_opAct] at hne
  obtain ⟨α, hα, β, hβ, hsum⟩ := HahnModule.support_smul_subset_vadd_support hne
  have hβγ : β < γ := by
    have hsum' : α + β = γ := hsum
    rw [← hsum']
    exact lt_add_of_pos_left β (pos_of_coeff_ne_zero hE hα)
  exact hβ (hx β hβγ)

/-- The coefficient of `(S + E) x` at an exponent `γ` below which `x` vanishes is `S x_γ`. -/
theorem coeff_perturbOp {S : Module.End k V} {E : (Module.End k V)⟦Γ⟧} (hE : 0 < E.orderTop)
    {x : HahnModule Γ k V} {γ : Γ} (hx : ∀ β < γ, ((HahnModule.of k).symm x).coeff β = 0) :
    ((HahnModule.of k).symm (perturbOp S E x)).coeff γ =
      S (((HahnModule.of k).symm x).coeff γ) := by
  rw [perturbOp_def, opAct_add, LinearMap.add_apply, HahnModule.of_symm_add, coeff_add,
    coeff_opAct_C, coeff_opAct_eq_zero hE hx, add_zero]

/-- `A = S + E` detects vanishing below any threshold `δ`: the coefficients of `A x` below `δ`
vanish exactly when those of `x` do. -/
theorem forall_lt_coeff_perturbOp_eq_zero_iff {S : Module.End k V}
    {E : (Module.End k V)⟦Γ⟧} (hS : Function.Injective S) (hE : 0 < E.orderTop)
    (x : HahnModule Γ k V) (δ : WithTop Γ) :
    (∀ β : Γ, (β : WithTop Γ) < δ →
        ((HahnModule.of k).symm (perturbOp S E x)).coeff β = 0) ↔
      ∀ β : Γ, (β : WithTop Γ) < δ → ((HahnModule.of k).symm x).coeff β = 0 := by
  constructor
  · intro h β hβ
    by_contra hne
    have hX : (HahnModule.of k).symm x ≠ 0 := ne_zero_of_coeff_ne_zero hne
    have hle : ((HahnModule.of k).symm x).order ≤ β := order_le_of_coeff_ne_zero hne
    have hA := coeff_perturbOp (S := S) hE (x := x) (γ := ((HahnModule.of k).symm x).order)
      fun β' hβ' => coeff_eq_zero_of_lt_order hβ'
    rw [h _ ((WithTop.coe_le_coe.mpr hle).trans_lt hβ)] at hA
    exact coeff_order_eq_zero.not.mpr hX (hS (hA.symm.trans (map_zero S).symm))
  · intro h β hβ
    rw [coeff_perturbOp hE fun β' hβ' => h β' ((WithTop.coe_lt_coe.mpr hβ').trans hβ),
      h β hβ, map_zero]

/-- `ihs:hh:thm:defect`, valuation: `v(Ax) = v(x)` for `A = S + E`. -/
theorem orderTop_perturbOp {S : Module.End k V} {E : (Module.End k V)⟦Γ⟧}
    (hS : Function.Injective S) (hE : 0 < E.orderTop) (x : HahnModule Γ k V) :
    ((HahnModule.of k).symm (perturbOp S E x)).orderTop =
      ((HahnModule.of k).symm x).orderTop := by
  apply le_antisymm
  · exact le_orderTop_iff_forall.mpr ((forall_lt_coeff_perturbOp_eq_zero_iff hS hE x _).mp
      fun j hj => coeff_eq_zero_of_lt_orderTop hj)
  · exact le_orderTop_iff_forall.mpr ((forall_lt_coeff_perturbOp_eq_zero_iff hS hE x _).mpr
      fun j hj => coeff_eq_zero_of_lt_orderTop hj)

/-- `ihs:hh:thm:defect`, leading coefficient: the leading coefficient of `Ax` is `S x_{v(x)}`. -/
theorem leadingCoeff_perturbOp {S : Module.End k V} {E : (Module.End k V)⟦Γ⟧}
    (hS : Function.Injective S) (hE : 0 < E.orderTop) (x : HahnModule Γ k V) :
    ((HahnModule.of k).symm (perturbOp S E x)).leadingCoeff =
      S ((HahnModule.of k).symm x).leadingCoeff := by
  by_cases hx : x = 0
  · rw [hx, map_zero (perturbOp S E), HahnModule.of_symm_zero, leadingCoeff_zero, map_zero S]
  have hX : (HahnModule.of k).symm x ≠ 0 := hx
  have hAX : (HahnModule.of k).symm (perturbOp S E x) ≠ 0 := by
    rw [← orderTop_ne_top, orderTop_perturbOp hS hE, orderTop_ne_top]
    exact hX
  have hord : ((HahnModule.of k).symm (perturbOp S E x)).order =
      ((HahnModule.of k).symm x).order := by
    have h := orderTop_perturbOp hS hE x
    rw [← order_eq_orderTop_of_ne_zero hAX, ← order_eq_orderTop_of_ne_zero hX] at h
    exact WithTop.coe_inj.mp h
  rw [leadingCoeff_eq, leadingCoeff_eq, hord,
    coeff_perturbOp hE fun β hβ => coeff_eq_zero_of_lt_order hβ]

end Order

section Defect

variable {Γ k V : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing k] [AddCommGroup V] [Module k V] {S : Module.End k V} {E : (Module.End k V)⟦Γ⟧}

omit [LinearOrder Γ] in
theorem opAct_sub [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ] (F G : (Module.End k V)⟦Γ⟧) :
    opAct (F - G) = opAct F - opAct G :=
  map_sub opActHom F G

/-- `ihs:hh:thm:defect`, injectivity: `A = S + E` is injective on `V((t^Γ))`. -/
theorem injective_perturbOp (hS : Function.Injective S) (hE : 0 < E.orderTop) :
    Function.Injective (perturbOp S E) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have h := orderTop_perturbOp hS hE x
  rw [hx, HahnModule.of_symm_zero, orderTop_zero, eq_comm, orderTop_eq_top] at h
  exact h

/-- The ordinary left inverse `U(Sv + w) = v` of `S` along a complement `W` of `Ran S`. -/
def leftInv (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) : Module.End k V :=
  LinearMap.linearProjOfIsCompl W S hS hW

theorem leftInv_mul (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) : leftInv hS hW * S = 1 :=
  LinearMap.ext fun v => LinearMap.linearProjOfIsCompl_apply_left W S hS hW v

theorem leftInv_apply_eq_zero_iff (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (v : V) : leftInv hS hW v = 0 ↔ v ∈ W := by
  rw [← LinearMap.mem_ker, leftInv, LinearMap.ker_linearProjOfIsCompl]

omit [AddCommGroup V] [Module k V] in
theorem orderTop_C_mul_pos {R : Type*} [Semiring R] (U : R) {F : R⟦Γ⟧} (hF : 0 < F.orderTop) :
    0 < (C U * F).orderTop := by
  rw [C_mul_eq_smul]
  exact hF.trans_le (orderTop_le_orderTop_smul U F)

/-- The left inverse `L = R U` of `A = S + E`, with `R = (I + UE)⁻¹ = ∑ (-UE)^n` the Neumann
inverse of `ihs:lem:neumann`. -/
def defectLeftInv (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) : (Module.End k V)⟦Γ⟧ :=
  (neumannFamily (C (leftInv hS hW) * E) (orderTop_C_mul_pos _ hE)).hsum * C (leftInv hS hW)

theorem C_leftInv_mul_C (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) :
    (C (leftInv hS hW) : (Module.End k V)⟦Γ⟧) * C S = 1 := by
  rw [← map_mul, leftInv_mul, map_one]

/-- `LA = R(US + UE) = R(I + UE) = I`. -/
theorem defectLeftInv_mul (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) :
    defectLeftInv hS hW hE * (C S + E) = 1 := by
  rw [defectLeftInv, mul_assoc, mul_add, C_leftInv_mul_C, hsum_neumannFamily_mul_one_add]

/-- `UΠ = U - UARU = U - (I + UE)RU = 0` for `Π = I - AL`. -/
theorem C_leftInv_mul_defectProj (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) :
    C (leftInv hS hW) * (1 - (C S + E) * defectLeftInv hS hW hE) = 0 := by
  rw [defectLeftInv, mul_sub, mul_one, ← mul_assoc, ← mul_assoc, mul_add, C_leftInv_mul_C,
    one_add_mul_hsum_neumannFamily, one_mul, sub_self]

/-- `W((t^Γ))` is the kernel of the coefficientwise extension of `U`. -/
theorem mem_hahnSubmodule_iff_opAct_C_leftInv (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (x : HahnModule Γ k V) :
    x ∈ hahnSubmodule W ↔ opAct (Γ := Γ) (C (leftInv hS hW)) x = 0 := by
  rw [mem_hahnSubmodule]
  constructor
  · intro h
    refine HahnModule.ext _ _ (funext fun γ => ?_)
    rw [coeff_opAct_C, (leftInv_apply_eq_zero_iff hS hW _).mpr (h γ), HahnModule.of_symm_zero,
      coeff_zero]
  · intro h γ
    rw [← leftInv_apply_eq_zero_iff hS hW, ← coeff_opAct_C, h, HahnModule.of_symm_zero,
      coeff_zero]

/-- `LA = I` on `V((t^Γ))`. -/
theorem opAct_defectLeftInv_perturbOp (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) (x : HahnModule Γ k V) :
    opAct (defectLeftInv hS hW hE) (perturbOp S E x) = x := by
  rw [perturbOp_def, ← Module.End.mul_apply, ← opAct_mul, defectLeftInv_mul, opAct_one,
    Module.End.one_apply]

/-- `L` vanishes on `W((t^Γ))`, since `U` does. -/
theorem opAct_defectLeftInv_eq_zero (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) {x : HahnModule Γ k V}
    (hx : x ∈ hahnSubmodule W) : opAct (defectLeftInv hS hW hE) x = 0 := by
  rw [defectLeftInv, opAct_mul, Module.End.mul_apply,
    (mem_hahnSubmodule_iff_opAct_C_leftInv hS hW x).mp hx, map_zero]

/-- The projection `Π = I - AL` of the proof of `ihs:hh:thm:defect`. -/
def defectProj (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) :
    Module.End k⟦Γ⟧ (HahnModule Γ k V) :=
  1 - perturbOp S E * opAct (defectLeftInv hS hW hE)

theorem defectProj_apply (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) (x : HahnModule Γ k V) :
    defectProj hS hW hE x = x - perturbOp S E (opAct (defectLeftInv hS hW hE) x) :=
  rfl

/-- `Π` takes values in `W((t^Γ)) = ker U`, because `UΠ = 0`. -/
theorem defectProj_mem (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) (x : HahnModule Γ k V) :
    defectProj hS hW hE x ∈ hahnSubmodule W := by
  have hP : defectProj hS hW hE = opAct (1 - (C S + E) * defectLeftInv hS hW hE) := by
    rw [defectProj, perturbOp_def, opAct_sub, opAct_one, opAct_mul]
  rw [mem_hahnSubmodule_iff_opAct_C_leftInv hS hW, hP, ← Module.End.mul_apply, ← opAct_mul,
    C_leftInv_mul_defectProj, opAct_zero, LinearMap.zero_apply]

/-- `Π` kills the range of `A`. -/
theorem defectProj_perturbOp (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) (y : HahnModule Γ k V) :
    defectProj hS hW hE (perturbOp S E y) = 0 := by
  rw [defectProj_apply, opAct_defectLeftInv_perturbOp, sub_self]

/-- `Π` is the identity on `W((t^Γ))`. -/
theorem defectProj_of_mem (hS : Function.Injective S) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) (hE : 0 < E.orderTop) {x : HahnModule Γ k V}
    (hx : x ∈ hahnSubmodule W) : defectProj hS hW hE x = x := by
  rw [defectProj_apply, opAct_defectLeftInv_eq_zero hS hW hE hx, map_zero, sub_zero]

/-- `ihs:hh:thm:defect`, `ihs:hh:eq:defectdecomp`: for injective `S`, `E` of positive order (or
zero) and an algebraic complement `V = Ran S ⊕ W`, the space `V((t^Γ))` is the direct sum of the
range of `A = S + E` and `W((t^Γ))`, through `x = ALx + Πx`. No commutation of `E` with `S` is
assumed. -/
theorem isCompl_range_perturbOp (hS : Function.Injective S) (hE : 0 < E.orderTop)
    {W : Submodule k V} (hW : IsCompl (LinearMap.range S) W) :
    IsCompl (LinearMap.range (perturbOp S E)) (hahnSubmodule W) := by
  refine ⟨Submodule.disjoint_def.mpr ?_,
    codisjoint_iff.mpr (Submodule.eq_top_iff'.mpr fun x => ?_)⟩
  · rintro _ ⟨y, rfl⟩ hy
    rw [← opAct_defectLeftInv_perturbOp hS hW hE y, opAct_defectLeftInv_eq_zero hS hW hE hy,
      map_zero]
  · refine Submodule.mem_sup.mpr ⟨_, ⟨opAct (defectLeftInv hS hW hE) x, rfl⟩, _,
      defectProj_mem hS hW hE x, ?_⟩
    rw [defectProj_apply, add_sub_cancel]

/-- `ihs:hh:thm:defect`: `coker A ≅ W((t^Γ))` as `k((t^Γ))`-modules, with `W((t^Γ))` realized as
the submodule `hahnSubmodule W` of `V((t^Γ))`; see `cokernelEquivHahnModule` for the Hahn module
`HahnModule Γ k W` itself. -/
def cokernelEquiv (hS : Function.Injective S) (hE : 0 < E.orderTop) {W : Submodule k V}
    (hW : IsCompl (LinearMap.range S) W) :
    (HahnModule Γ k V ⧸ LinearMap.range (perturbOp S E)) ≃ₗ[k⟦Γ⟧] hahnSubmodule (Γ := Γ) W :=
  Submodule.quotientEquivOfIsCompl _ _ (isCompl_range_perturbOp hS hE hW)

/-- `ihs:hh:thm:defect`: `coker A ≅ W((t^Γ))` as `k((t^Γ))`-modules, with `W((t^Γ))` the Hahn
module `HahnModule Γ k W` of `W`-valued series. -/
def cokernelEquivHahnModule (hS : Function.Injective S) (hE : 0 < E.orderTop)
    {W : Submodule k V} (hW : IsCompl (LinearMap.range S) W) :
    (HahnModule Γ k V ⧸ LinearMap.range (perturbOp S E)) ≃ₗ[k⟦Γ⟧] HahnModule Γ k W :=
  (cokernelEquiv hS hE hW).trans (hahnSubmoduleEquiv W).symm

/-- A vector outside `Ran S` stays, as a constant series, outside the range of `A = S + E`: if
`Ax = f`, then `x` vanishes below `0` and `f = (Ax)_0 = S x_0`. -/
theorem single_notMem_range_perturbOp (hS : Function.Injective S) (hE : 0 < E.orderTop)
    {f : V} (hf : f ∉ LinearMap.range S) :
    HahnModule.of k (single (0 : Γ) f) ∉ LinearMap.range (perturbOp S E) := by
  rintro ⟨x, hx⟩
  have hlow := (forall_lt_coeff_perturbOp_eq_zero_iff hS hE x ((0 : Γ) : WithTop Γ)).mp
    fun β hβ => by
      rw [hx, Equiv.symm_apply_apply, coeff_single_of_ne (WithTop.coe_lt_coe.mp hβ).ne]
  have h0 := coeff_perturbOp (S := S) hE (x := x) (γ := 0)
    fun β hβ => hlow β (WithTop.coe_lt_coe.mpr hβ)
  rw [hx, Equiv.symm_apply_apply, coeff_single_same] at h0
  exact hf ⟨_, h0.symm⟩

/-- `ihs:hh:cor:norepair`: an injective nonsurjective `S` cannot become surjective on
`V((t^Γ))` by adding any positive-order `E`, commuting with `S` or not, with any (possibly
infinite) support. -/
theorem not_surjective_perturbOp (hS : Function.Injective S) (hE : 0 < E.orderTop)
    (hns : ¬ Function.Surjective S) : ¬ Function.Surjective (perturbOp S E) := by
  intro hA
  obtain ⟨f, hf⟩ : ∃ f, f ∉ LinearMap.range S := by
    by_contra hall
    push Not at hall
    exact hns fun f => LinearMap.mem_range.mp (hall f)
  exact single_notMem_range_perturbOp hS hE hf (LinearMap.mem_range.mpr (hA _))

/-- `ihs:hh:cor:independent`: if the classes of `f_j` in `V / Ran S` are linearly independent
over `k`, then the classes of their constant extensions in `V((t^Γ)) / (S + E)V((t^Γ))` are
linearly independent over `k((t^Γ))`. -/
theorem linearIndependent_mkQ_single (hS : Function.Injective S) (hE : 0 < E.orderTop)
    {ι : Type*} {f : ι → V} (hf : LinearIndependent k fun i => (LinearMap.range S).mkQ (f i)) :
    LinearIndependent k⟦Γ⟧ fun i =>
      (LinearMap.range (perturbOp S E)).mkQ (HahnModule.of k (single (0 : Γ) (f i))) := by
  classical
  rw [linearIndependent_iff'] at hf ⊢
  intro s g hsum i hi
  by_contra hgi
  -- the least exponent `δ` among the nonzero coefficients `g j`
  obtain ⟨j₀, hj₀, hmin⟩ := (s.filter fun j => g j ≠ 0).exists_min_image (fun j => (g j).order)
    ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  rw [Finset.mem_filter] at hj₀
  have hy : (∑ j ∈ s, g j • HahnModule.of k (single (0 : Γ) (f j))) ∈
      LinearMap.range (perturbOp S E) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
    simpa only [map_smul] using hsum
  obtain ⟨x, hx⟩ := hy
  have hcoeff : ∀ γ, ((HahnModule.of k).symm (perturbOp S E x)).coeff γ =
      ∑ j ∈ s, (g j).coeff γ • f j := by
    intro γ
    rw [hx, of_symm_sum, coeff_sum]
    exact Finset.sum_congr rfl fun j _ => coeff_smul_single_zero (g j) (f j) γ
  -- below `δ` the sum vanishes, hence so does `x`
  have hlow := (forall_lt_coeff_perturbOp_eq_zero_iff hS hE x ((g j₀).order : WithTop Γ)).mp
    fun β hβ => by
      rw [hcoeff]
      refine Finset.sum_eq_zero fun j hj => ?_
      by_cases hgj : g j = 0
      · rw [hgj, coeff_zero, zero_smul]
      · rw [coeff_eq_zero_of_lt_order ((WithTop.coe_lt_coe.mp hβ).trans_le
          (hmin j (Finset.mem_filter.mpr ⟨hj, hgj⟩))), zero_smul]
  -- so the coefficient at `δ` is `S x_δ ∈ Ran S`
  have hδ := coeff_perturbOp (S := S) hE (x := x) (γ := (g j₀).order)
    fun β hβ => hlow β (WithTop.coe_lt_coe.mpr hβ)
  rw [hcoeff] at hδ
  have hmk : (LinearMap.range S).mkQ (∑ j ∈ s, (g j).coeff (g j₀).order • f j) = 0 := by
    rw [hδ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self S _
  rw [map_sum] at hmk
  simp only [map_smul] at hmk
  exact coeff_order_eq_zero.not.mpr hj₀.2
    (hf s (fun j => (g j).coeff (g j₀).order) hmk j₀ hj₀.1)

end Defect

section Rank

universe u v w

variable {Γ : Type u} {k : Type v} {V : Type w} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [Field k] [AddCommGroup V] [Module k V] {S : Module.End k V}
  {E : (Module.End k V)⟦Γ⟧}

/-- `ihs:hh:cor:independent`, dimension bound: `dim_K coker(S + E) ≥ dim_k (V / Ran S)` for
`K = k((t^Γ))`, with both cardinals lifted to a common universe. -/
theorem lift_rank_quotient_le_rank_coker (hS : Function.Injective S)
    (hE : 0 < E.orderTop) :
    Cardinal.lift.{u} (Module.rank k (V ⧸ LinearMap.range S)) ≤
      Module.rank k⟦Γ⟧ (HahnModule Γ k V ⧸ LinearMap.range (perturbOp S E)) := by
  let b := Module.Basis.ofVectorSpace k (V ⧸ LinearMap.range S)
  choose f hf using fun i => (LinearMap.range S).mkQ_surjective (b i)
  have hli : LinearIndependent k fun i => (LinearMap.range S).mkQ (f i) := by
    simpa only [hf] using b.linearIndependent
  have h := (linearIndependent_mkQ_single (Γ := Γ) hS hE hli).cardinal_lift_le_rank
  rwa [b.mk_eq_rank'', Cardinal.lift_id'.{w, u}, Cardinal.lift_umax.{w, u}] at h

end Rank

section Continuum

open Surreal.ContinuumDefects
open scoped lp

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- Applying a zero-preserving map to the coefficients does not lower the order. -/
theorem orderTop_map_pos [Zero Γ] {R R' F : Type*} [Zero R] [Zero R'] [FunLike F R R']
    [ZeroHomClass F R R'] (φ : F) {E : R⟦Γ⟧} (hE : 0 < E.orderTop) : 0 < (E.map φ).orderTop :=
  hE.trans_le (le_orderTop_iff_forall.mpr fun j hj => by
    rw [map_coeff, coeff_eq_zero_of_lt_orderTop hj, map_zero])

/-- The harmonic diagonal operator `D e_n = n⁻¹ e_n` in the source indexing, as an algebraic
endomorphism: on `ℓ²(ℕ, ℂ)` it is `e_n ↦ (n + 1)⁻¹ e_n` (see `ContinuumDefects`). -/
abbrev invDiagEnd : Module.End ℂ ℓ²(ℕ, ℂ) :=
  (invDiag : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)).toLinearMap

theorem injective_invDiagEnd : Function.Injective invDiagEnd :=
  invDiag_injective

theorem injective_invDiagEnd_sq :
    Function.Injective (invDiag * invDiag : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)).toLinearMap :=
  fun _ _ h => invDiag_injective (invDiag_injective h)

/-- `ihs:hh:thm:continuum`, algebraic form: for every `E ∈ End_ℂ(H)((t^Γ))` of positive order
(zero included), `dim_K coker(D + E) ≥ 2^ℵ₀` on `H((t^Γ))`, `H = ℓ²`, `K = ℂ((t^Γ))`. -/
theorem continuum_le_rank_coker_invDiag {E : (Module.End ℂ ℓ²(ℕ, ℂ))⟦Γ⟧}
    (hE : 0 < E.orderTop) :
    Cardinal.continuum ≤
      Module.rank ℂ⟦Γ⟧ (HahnModule Γ ℂ ℓ²(ℕ, ℂ) ⧸ LinearMap.range (perturbOp invDiagEnd E)) := by
  have h := (linearIndependent_mkQ_single (Γ := Γ) injective_invDiagEnd hE
    linearIndependent_powerVec_mkQ).cardinal_lift_le_rank
  rwa [Cardinal.mk_Ioc_real (by norm_num), Cardinal.lift_continuum, Cardinal.lift_uzero] at h

/-- `ihs:hh:thm:continuum`, algebraic form with leading operator `D²`. -/
theorem continuum_le_rank_coker_invDiag_sq {E : (Module.End ℂ ℓ²(ℕ, ℂ))⟦Γ⟧}
    (hE : 0 < E.orderTop) :
    Cardinal.continuum ≤ Module.rank ℂ⟦Γ⟧ (HahnModule Γ ℂ ℓ²(ℕ, ℂ) ⧸
      LinearMap.range (perturbOp (invDiag * invDiag : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)).toLinearMap E)) := by
  have h := (linearIndependent_mkQ_single (Γ := Γ) injective_invDiagEnd_sq hE
    linearIndependent_powerVec_mkQ_sq).cardinal_lift_le_rank
  rwa [Cardinal.mk_Ioc_real (by norm_num), Cardinal.lift_continuum, Cardinal.lift_uzero] at h

/-- `ihs:hh:thm:continuum`: for every `E ∈ B(H)((t^Γ))` of positive order (zero included), with
`H = ℓ²` and `D e_n = n⁻¹ e_n`, `dim_K coker(D + E) ≥ 2^ℵ₀`, and the same holds with leading
operator `D²`. Here `B(H)((t^Γ))` acts on `H((t^Γ))` by convolution through the coefficientwise
inclusion `B(H) → End_ℂ(H)`. -/
theorem continuum_le_rank_coker {E : (ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ))⟦Γ⟧} (hE : 0 < E.orderTop) :
    Cardinal.continuum ≤ Module.rank ℂ⟦Γ⟧ (HahnModule Γ ℂ ℓ²(ℕ, ℂ) ⧸
        LinearMap.range (perturbOp invDiagEnd (E.map ContinuousLinearMap.toLinearMapRingHom))) ∧
      Cardinal.continuum ≤ Module.rank ℂ⟦Γ⟧ (HahnModule Γ ℂ ℓ²(ℕ, ℂ) ⧸
        LinearMap.range (perturbOp (invDiag * invDiag : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)).toLinearMap
          (E.map ContinuousLinearMap.toLinearMapRingHom))) :=
  ⟨continuum_le_rank_coker_invDiag (orderTop_map_pos _ hE),
    continuum_le_rank_coker_invDiag_sq (orderTop_map_pos _ hE)⟩

end Continuum

end

end Surreal.DefectRigidity
