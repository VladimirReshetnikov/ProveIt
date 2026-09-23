import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.CharP.Algebra

/-!
# The Euler derivation on Hahn fields and transcendence of the logarithm

This file formalizes the Hahn-field content of `diff:rs:lem:euler` and `diff:rs:lem:tautrans`
in `docs/surcomplex/differential-equations/article.tex`, following the corrected statement of
`diff:rs:lem:euler` (the Euler derivative can delete the constant term, so its support is only
contained in the original support, and `∂ = -t ∂_T` preserves `K_Γ` exactly when `Γ = {0}` or
`1 ∈ Γ`).

## Generic Hahn rings

Let `Γ` be an ordered cancellative commutative monoid, `R` a commutative ring and
`φ : Γ →+ R` an additive exponent map. `euler φ` is the `R`-linear derivation
`∑ c_γ t^γ ↦ ∑ φ(γ) c_γ t^γ` of `R((t^Γ))` (`diff:rs:eq:eulerhahn`; the Leibniz rule is checked
coefficientwise on antidiagonals). Proved about it:

* `euler_single`: `∂_T (r t^a) = φ(a) r t^a`;
* `support_euler_subset`: the support of `∂_T f` lies in the support of `f` minus `{0}`;
* `euler_eq_zero_iff`, `euler_eq_zero_iff_exists`: if `φ` vanishes only at `0` and `R` has no
  zero divisors, the constants are exactly the constant series `C r`;
* `orderTop_le_orderTop_euler`, `zero_lt_orderTop_euler`: `∂_T` never lowers the order, and maps
  `{f = 0 ∨ v f ≥ 0}` into `{f = 0 ∨ v f > 0}`, with no hypothesis on `φ`;
* `euler_embDomain`, `euler_subgroupEmb`, `euler_mem_hahnSubring`: for an additive subgroup
  `Γ₀` of an ordered group `Γ`, the copy `hahnSubring Γ₀` of `R((t^{Γ₀}))` in `R((t^Γ))`
  (characterized by `mem_hahnSubring_iff` as the series supported in `Γ₀`) is `∂_T`-stable, and
  `∂_T` restricts there to the Euler derivation of `R((t^{Γ₀}))`;
* `intrinsic_mem_hahnSubring_iff`: the rescaled derivation `intrinsic φ e = -t^e ∂_T` preserves
  `hahnSubring Γ₀` exactly when `Γ₀ = ⊥` or `e ∈ Γ₀`, provided `φ` vanishes only at `0`;
* `euler_ne_one`: no element of `R((t^Γ))` has Euler derivative `1`, since the `t^0`
  coefficient of every Euler derivative vanishes.

## Transcendence

`transcendental_of_deriv_eq_one` is the argument of `diff:rs:lem:tautrans` for an arbitrary
differential field extension `L / K` with `K` of characteristic zero: if no element of `K` has
derivative `1`, every `τ ∈ L` with `τ′ = 1` is transcendental over `K`. The proof differentiates
the monic minimal polynomial, as in the source, with `Differential.deriv_aeval_eq`.
`transcendental_of_derivation_eq_one` is the same statement with explicit derivations, and
`transcendental_of_euler` applies it to every Hahn field `R((t^Γ))` of characteristic zero.

## Real exponents

For `K_ℝ = ℂ((t^ℝ))`, `derT` is the Euler derivation `∂_T`, *defined* by its coefficient
formula `diff:rs:eq:eulerhahn`; `derTOn Γ` is the same coefficientwise derivation on
`K_Γ = ℂ((t^Γ))` for an arbitrary additive subgroup `Γ ⊆ ℝ`, `hahnSubfield Γ` is the copy of
`K_Γ` inside `K_ℝ`, and `der = -t ∂_T` is defined from `derT`. These are Hahn-field models of
the surreal operators; their identification with the surreal `∂_T` and `∂` is pending (see
below). The Hahn-field clauses of `diff:rs:lem:euler` are `coeff_derT`, `coeff_derTOn` (the
formula, which holds here by definition), `derT_subgroupEmb` and `derT_mem_hahnSubfield`
(stability of every `K_Γ`), `derTOn_eq_zero_iff` and `derT_eq_zero_iff` (the constants are
`ℂ`), `zero_lt_orderTop_derTOn` and `zero_lt_orderTop_derT` (the valuation clause), `der_single`
(`∂ t^a = -a t^{a+1}`, here a consequence of the definitions) and `der_mem_hahnSubfield_iff`
(`∂` preserves `K_Γ` iff `Γ = {0}` or `1 ∈ Γ`). The Hahn-field clauses of
`diff:rs:lem:tautrans` are `derT_ne_one` and `transcendental_tau`: no element of `K_ℝ` has
`∂_T`-derivative `1`, and in every differential field extension of `(K_ℝ, ∂_T)` a primitive `τ`
of `1` is transcendental over `K_ℝ`. The clause `∂_T τ = 1` of `diff:rs:eq:eulerhahn` for
`τ = log t` is not formalized.

## Pending

The surreal realization is not proved here: that `K_Γ ⊆ No[i]` and that the surreal Euler
derivation `∂_T = -ω ∂` (from the Berarducci–Mantova derivation, via `diff:BM:additive` and the
real-power rule) restricts to `derT` on `K_ℝ`, and that `τ = log t ∈ No[i]` satisfies
`∂_T τ = 1`. In particular the formula `diff:rs:eq:eulerhahn` and the real-power rule
`der_single` are proved only for the coefficientwise model, not derived from the surreal
derivation. Once these are available, `transcendental_tau` gives the transcendence of `log t`
over `K_ℝ` inside `No[i]` directly.
-/

namespace Surreal.EulerDerivation

open HahnSeries

noncomputable section

section Definition

variable {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ] {R : Type*} [CommRing R]

/-- The coefficientwise Euler operator `∑ c_γ t^γ ↦ ∑ φ(γ) c_γ t^γ` on `R((t^Γ))`, for an
additive exponent map `φ : Γ →+ R`. -/
def eulerFun (φ : Γ →+ R) (f : HahnSeries Γ R) : HahnSeries Γ R where
  coeff γ := φ γ * f.coeff γ
  isPWO_support' := f.isPWO_support.mono fun _ h => right_ne_zero_of_mul h

@[simp]
theorem coeff_eulerFun (φ : Γ →+ R) (f : HahnSeries Γ R) (γ : Γ) :
    (eulerFun φ f).coeff γ = φ γ * f.coeff γ := rfl

theorem support_eulerFun_subset (φ : Γ →+ R) (f : HahnSeries Γ R) :
    (eulerFun φ f).support ⊆ f.support := fun _ h => right_ne_zero_of_mul h

variable [IsOrderedCancelAddMonoid Γ]

/-- The Euler derivation `∂_T (∑ c_γ t^γ) = ∑ φ(γ) c_γ t^γ` of `diff:rs:eq:eulerhahn`, as an
`R`-linear derivation of `R((t^Γ))`. -/
def euler (φ : Γ →+ R) : Derivation R (HahnSeries Γ R) (HahnSeries Γ R) :=
  Derivation.mk'
    { toFun := eulerFun φ
      map_add' := fun f g => by ext γ; simp [HahnSeries.coeff_add, mul_add]
      map_smul' := fun r f => by ext γ; simp [mul_left_comm] }
    fun f g => by
      ext a
      simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, HahnSeries.coeff_add,
        coeff_eulerFun]
      rw [coeff_mul_right' g.isPWO_support (support_eulerFun_subset φ g), mul_comm g,
        coeff_mul_left' f.isPWO_support (support_eulerFun_subset φ f), coeff_mul,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ij hij => ?_
      obtain ⟨-, -, h⟩ := Finset.mem_antidiagonal.1 hij
      simp only [coeff_eulerFun]
      rw [← h, map_add]
      ring

@[simp]
theorem coeff_euler (φ : Γ →+ R) (f : HahnSeries Γ R) (γ : Γ) :
    (euler φ f).coeff γ = φ γ * f.coeff γ := rfl

theorem euler_apply (φ : Γ →+ R) (f : HahnSeries Γ R) : euler φ f = eulerFun φ f := rfl

/-- The Euler derivative of a monomial: `∂_T (r t^a) = φ(a) r t^a`. -/
theorem euler_single (φ : Γ →+ R) (a : Γ) (r : R) :
    euler φ (single a r) = single a (φ a * r) := by
  ext γ
  by_cases h : γ = a
  · subst h
    simp
  · simp [coeff_single_of_ne h]

/-- The support of an Euler derivative is contained in the original support with the exponent
`0` removed: the derivative can only delete coefficients. -/
theorem support_euler_subset (φ : Γ →+ R) (f : HahnSeries Γ R) :
    (euler φ f).support ⊆ f.support \ {0} := by
  intro γ h
  rw [mem_support, coeff_euler] at h
  refine ⟨(mem_support _ _).2 (right_ne_zero_of_mul h), fun h0 => h ?_⟩
  rw [Set.mem_singleton_iff] at h0
  rw [h0, map_zero, zero_mul]

/-- The `t^0` coefficient of every Euler derivative vanishes. -/
theorem coeff_zero_euler (φ : Γ →+ R) (f : HahnSeries Γ R) : (euler φ f).coeff 0 = 0 := by
  simp

/-- Constants are killed by the Euler derivation. -/
theorem euler_C (φ : Γ →+ R) (r : R) : euler φ (C r) = 0 := by
  rw [C_eq_algebraMap]
  exact (euler φ).map_algebraMap r

/-- `diff:rs:lem:tautrans`, first clause, for every exponent map: no element of `R((t^Γ))` has
Euler derivative `1`, because the `t^0` coefficient of an Euler derivative vanishes. -/
theorem euler_ne_one [Nontrivial R] (φ : Γ →+ R) (f : HahnSeries Γ R) : euler φ f ≠ 1 := by
  intro h
  have h0 := congrArg (fun g : HahnSeries Γ R => g.coeff 0) h
  simp only [coeff_zero_euler, coeff_one] at h0
  exact zero_ne_one h0

/-- `diff:rs:lem:euler`, the constants: if `φ` vanishes only at `0` and `R` has no zero
divisors, then the constants of the Euler derivation are exactly the constant series. -/
theorem euler_eq_zero_iff [NoZeroDivisors R] {φ : Γ →+ R} (hφ : ∀ γ, φ γ = 0 → γ = 0)
    (f : HahnSeries Γ R) : euler φ f = 0 ↔ f = C (f.coeff 0) := by
  constructor
  · intro h
    ext γ
    by_cases hγ : γ = 0
    · subst hγ
      simp
    · have h' := congrArg (fun g : HahnSeries Γ R => g.coeff γ) h
      simp only [coeff_euler, HahnSeries.coeff_zero] at h'
      rw [C_apply, coeff_single_of_ne hγ]
      exact (mul_eq_zero.1 h').resolve_left fun h'' => hγ (hφ γ h'')
  · intro h
    rw [h, euler_C]

/-- `diff:rs:lem:euler`, the constants, in range form. -/
theorem euler_eq_zero_iff_exists [NoZeroDivisors R] {φ : Γ →+ R} (hφ : ∀ γ, φ γ = 0 → γ = 0)
    (f : HahnSeries Γ R) : euler φ f = 0 ↔ ∃ c : R, C c = f := by
  rw [euler_eq_zero_iff hφ]
  exact ⟨fun h => ⟨_, h.symm⟩, fun ⟨c, hc⟩ => by rw [← hc, C_apply, coeff_single_same, C_apply]⟩

end Definition

section Order

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  {R : Type*} [CommRing R]

/-- The Euler derivation never lowers the order. -/
theorem orderTop_le_orderTop_euler (φ : Γ →+ R) (f : HahnSeries Γ R) :
    f.orderTop ≤ (euler φ f).orderTop := by
  rw [le_orderTop_iff_forall]
  intro j hj
  rw [coeff_euler, coeff_eq_zero_of_lt_orderTop hj, mul_zero]

/-- `diff:rs:lem:euler`, the valuation clause: the Euler derivation maps
`{f : f = 0 ∨ v f ≥ 0}` into `{f : f = 0 ∨ v f > 0}`. -/
theorem zero_lt_orderTop_euler (φ : Γ →+ R) {f : HahnSeries Γ R} (hf : 0 ≤ f.orderTop) :
    0 < (euler φ f).orderTop := by
  refine lt_of_le_of_ne (hf.trans (orderTop_le_orderTop_euler φ f)) fun h => ?_
  exact coeff_orderTop_ne h.symm (coeff_zero_euler φ f)

end Order

section Embedding

variable {Γ Γ' : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [AddCommMonoid Γ'] [PartialOrder Γ'] [IsOrderedCancelAddMonoid Γ'] {R : Type*} [CommRing R]

/-- Compatibility of Euler derivations with an embedding of exponent monoids: the Euler
derivation of `R((t^Γ'))` preserves the image of `R((t^Γ))` and restricts there to the Euler
derivation of `R((t^Γ))` for the restricted exponent map. -/
theorem euler_embDomain (ι : Γ ↪o Γ') {φ' : Γ' →+ R} {φ : Γ →+ R} (h : ∀ γ, φ' (ι γ) = φ γ)
    (f : HahnSeries Γ R) : euler φ' (embDomain ι f) = embDomain ι (euler φ f) := by
  ext b
  by_cases hb : b ∈ Set.range ι
  · obtain ⟨a, rfl⟩ := hb
    simp [embDomain_coeff, h]
  · simp [embDomain_notin_range hb]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [AddCommMonoid Γ']
  [IsOrderedCancelAddMonoid Γ'] in
/-- The image of `R((t^Γ))` in `R((t^Γ'))` consists of the series supported in `ι(Γ)`. -/
theorem mem_range_embDomain_iff (ι : Γ ↪o Γ') (f : HahnSeries Γ' R) :
    f ∈ Set.range (embDomain ι : HahnSeries Γ R → HahnSeries Γ' R) ↔
      f.support ⊆ Set.range ι := by
  constructor
  · rintro ⟨g, rfl⟩
    exact support_embDomain_subset.trans (Set.image_subset_range _ _)
  · intro h
    refine ⟨⟨fun a => f.coeff (ι a), ?_⟩, ?_⟩
    · have hs := f.isPWO_support
      rw [Set.IsPWO, Set.partiallyWellOrderedOn_iff_exists_lt] at hs ⊢
      intro g hg
      obtain ⟨m, n, hmn, hle⟩ := hs (fun k => ι (g k)) hg
      exact ⟨m, n, hmn, ι.le_iff_le.1 hle⟩
    · ext b
      by_cases hb : b ∈ Set.range ι
      · obtain ⟨a, rfl⟩ := hb
        rw [embDomain_coeff]
      · rw [embDomain_notin_range hb]
        by_contra hne
        exact hb (h ((mem_support _ _).2 (Ne.symm hne)))

end Embedding

section Subgroup

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {R : Type*} [CommRing R]

/-- The inclusion `Γ₀ ↪o Γ` of an additive subgroup. -/
def subgroupEmbedding (Γ₀ : AddSubgroup Γ) : Γ₀ ↪o Γ := OrderEmbedding.subtype (· ∈ Γ₀)

omit [IsOrderedAddMonoid Γ] in
theorem range_subgroupEmbedding (Γ₀ : AddSubgroup Γ) :
    Set.range (subgroupEmbedding Γ₀) = (Γ₀ : Set Γ) := by
  ext x
  simp [subgroupEmbedding]

/-- The embedding `R((t^Γ₀)) → R((t^Γ))` of Hahn rings for a subgroup `Γ₀ ⊆ Γ`. -/
def subgroupEmb (Γ₀ : AddSubgroup Γ) : HahnSeries Γ₀ R →+* HahnSeries Γ R :=
  embDomainRingHom Γ₀.subtype Subtype.coe_injective fun _ _ => Iff.rfl

theorem subgroupEmb_apply (Γ₀ : AddSubgroup Γ) (f : HahnSeries Γ₀ R) :
    subgroupEmb Γ₀ f = embDomain (subgroupEmbedding Γ₀) f := rfl

/-- `K_{Γ₀} = R((t^{Γ₀}))`, as a subring of `R((t^Γ))`. -/
def hahnSubring (Γ₀ : AddSubgroup Γ) : Subring (HahnSeries Γ R) := (subgroupEmb Γ₀).range

/-- `K_{Γ₀}` consists exactly of the series of `R((t^Γ))` whose support lies in `Γ₀`. -/
theorem mem_hahnSubring_iff {Γ₀ : AddSubgroup Γ} {f : HahnSeries Γ R} :
    f ∈ hahnSubring Γ₀ ↔ f.support ⊆ Γ₀ := by
  rw [hahnSubring, RingHom.mem_range, ← range_subgroupEmbedding,
    ← mem_range_embDomain_iff]
  rfl

/-- `diff:rs:lem:euler`, stability: every Euler derivation of `R((t^Γ))` preserves every
`K_{Γ₀}`. -/
theorem euler_mem_hahnSubring (φ : Γ →+ R) {Γ₀ : AddSubgroup Γ} {f : HahnSeries Γ R}
    (hf : f ∈ hahnSubring Γ₀) : euler φ f ∈ hahnSubring Γ₀ := by
  rw [mem_hahnSubring_iff] at hf ⊢
  exact (support_euler_subset φ f).trans (Set.sdiff_subset.trans hf)

/-- `diff:rs:lem:euler`, restriction: the Euler derivation of `R((t^Γ))` restricts on
`K_{Γ₀}` to the Euler derivation of `R((t^{Γ₀}))` with the restricted exponent map. -/
theorem euler_subgroupEmb (φ : Γ →+ R) (Γ₀ : AddSubgroup Γ) (f : HahnSeries Γ₀ R) :
    euler φ (subgroupEmb Γ₀ f) = subgroupEmb Γ₀ (euler (φ.comp Γ₀.subtype) f) := by
  rw [subgroupEmb_apply, subgroupEmb_apply]
  exact euler_embDomain _ (fun _ => rfl) f

/-- The rescaled derivation `∂ = -t^e ∂_T` of `R((t^Γ))`. For `Γ = ℝ` and `e = 1` it models, on
`K_ℝ`, the surreal derivation `∂ = -t ∂_T` of `diff:rs:eq:euler`; the identification with the
restriction of the Berarducci–Mantova derivation is pending. -/
def intrinsic (φ : Γ →+ R) (e : Γ) : Derivation R (HahnSeries Γ R) (HahnSeries Γ R) :=
  (-single e (1 : R)) • euler φ

theorem intrinsic_apply (φ : Γ →+ R) (e : Γ) (f : HahnSeries Γ R) :
    intrinsic φ e f = -single e 1 * euler φ f := rfl

/-- The rescaled derivative of a monomial: `-t^e ∂_T (r t^a) = -φ(a) r t^{e+a}`. -/
theorem intrinsic_single (φ : Γ →+ R) (e a : Γ) (r : R) :
    intrinsic φ e (single a r) = single (e + a) (-(φ a * r)) := by
  rw [intrinsic_apply, euler_single, neg_mul, single_mul_single, one_mul]
  ext b
  by_cases hb : b = e + a
  · subst hb
    rw [HahnSeries.coeff_neg, coeff_single_same, coeff_single_same]
  · rw [HahnSeries.coeff_neg, coeff_single_of_ne hb, coeff_single_of_ne hb, neg_zero]

/-- `diff:rs:lem:euler`, the corrected criterion: `∂ = -t^e ∂_T` preserves `K_{Γ₀}` exactly
when `Γ₀ = {0}` or `e ∈ Γ₀`, as soon as `φ` vanishes only at `0`. -/
theorem intrinsic_mem_hahnSubring_iff {φ : Γ →+ R} (hφ : ∀ γ, φ γ = 0 → γ = 0)
    (Γ₀ : AddSubgroup Γ) (e : Γ) :
    (∀ f ∈ hahnSubring (R := R) Γ₀, intrinsic φ e f ∈ hahnSubring Γ₀) ↔
      Γ₀ = ⊥ ∨ e ∈ Γ₀ := by
  simp only [mem_hahnSubring_iff]
  constructor
  · intro H
    by_contra hcon
    push Not at hcon
    obtain ⟨hne, he⟩ := hcon
    obtain ⟨γ, hγ, hγ0⟩ : ∃ γ ∈ Γ₀, γ ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hne ((AddSubgroup.eq_bot_iff_forall Γ₀).2 h')
    have hf : (single γ (1 : R)).support ⊆ Γ₀ :=
      support_single_subset.trans (Set.singleton_subset_iff.2 hγ)
    have hmem : e + γ ∈ (intrinsic φ e (single γ (1 : R))).support := by
      rw [intrinsic_single, mem_support, coeff_single_same, mul_one, neg_ne_zero]
      exact fun h => hγ0 (hφ γ h)
    exact he ((AddSubgroup.add_mem_cancel_right Γ₀ hγ).1 (H _ hf hmem))
  · rintro (h | he) f hf
    · have hzero : euler φ f = 0 := by
        ext γ
        rw [coeff_euler, HahnSeries.coeff_zero]
        by_cases hγ : f.coeff γ = 0
        · rw [hγ, mul_zero]
        · have hγ' := hf ((mem_support _ _).2 hγ)
          rw [h, SetLike.mem_coe, AddSubgroup.mem_bot] at hγ'
          rw [hγ', map_zero, zero_mul]
      rw [intrinsic_apply, hzero, mul_zero, support_zero]
      exact Set.empty_subset _
    · intro γ hγ
      rw [intrinsic_apply] at hγ
      obtain ⟨x, hx, y, hy, rfl⟩ := support_mul_subset hγ
      rw [support_neg] at hx
      have hxe : x = e := support_single_subset hx
      rw [hxe]
      exact Γ₀.add_mem he (hf (support_euler_subset φ f hy).1)

end Subgroup

section Field

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  {R : Type*} [Field R]

/-- `K_{Γ₀} = R((t^{Γ₀}))`, as a subfield of `R((t^Γ))`. -/
def hahnSubfield (Γ₀ : AddSubgroup Γ) : Subfield (HahnSeries Γ R) := (subgroupEmb Γ₀).fieldRange

theorem mem_hahnSubfield_iff {Γ₀ : AddSubgroup Γ} {f : HahnSeries Γ R} :
    f ∈ hahnSubfield Γ₀ ↔ f.support ⊆ Γ₀ := by
  rw [← mem_hahnSubring_iff]
  rfl

end Field

section Transcendence

open Polynomial
open scoped Differential

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- `diff:rs:lem:tautrans`, the transcendence argument, for an arbitrary differential field
extension `L / K` of characteristic zero: if no element of `K` has derivative `1`, then every
`τ ∈ L` with `τ′ = 1` is transcendental over `K`. Differentiating the monic minimal polynomial
`P` of `τ` gives the lower-degree relation `(P^∂ + P′)(τ) = 0`, whose `X^{d-1}` coefficient
yields `(-a_{d-1}/d)′ = 1`. -/
theorem transcendental_of_deriv_eq_one [CharZero K] [Differential K] [Differential L]
    [DifferentialAlgebra K L] (hK : ∀ k : K, k′ ≠ 1) {τ : L} (hτ : τ′ = 1) :
    Transcendental K τ := by
  intro halg
  have hint : IsIntegral K τ := halg.isIntegral
  set P := minpoly K τ
  have hmonic : P.Monic := minpoly.monic hint
  have hpos : 0 < P.natDegree := minpoly.natDegree_pos hint
  set Q : K[X] := Differential.mapCoeffs P + derivative P with hQdef
  have hQτ : aeval τ Q = 0 := by
    have h := Differential.deriv_aeval_eq τ P
    rw [minpoly.aeval, map_zero, hτ, mul_one] at h
    rw [hQdef, map_add]
    exact h.symm
  have hQcoeff : ∀ m, Q.coeff m = (P.coeff m)′ + P.coeff (m + 1) * (m + 1) := by
    intro m
    rw [hQdef, Polynomial.coeff_add, Differential.coeff_mapCoeffs, coeff_derivative]
  have hQdeg : Q.degree < P.degree := by
    rw [degree_eq_natDegree hmonic.ne_zero, degree_lt_iff_coeff_zero]
    intro m hm
    rw [hQcoeff, coeff_eq_zero_of_natDegree_lt (show P.natDegree < m + 1 by omega), zero_mul,
      add_zero]
    rcases hm.eq_or_lt with h | h
    · rw [← h, hmonic.coeff_natDegree, Derivation.map_one_eq_zero]
    · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
  have hQ0 : Q = 0 := by
    by_contra hne
    exact absurd (minpoly.degree_le_of_ne_zero K τ hne hQτ) (not_le.2 hQdeg)
  set n := P.natDegree
  have hc := hQcoeff (n - 1)
  have hcast : ((n - 1 : ℕ) : K) + 1 = n := by
    rw [Nat.cast_sub hpos, Nat.cast_one, sub_add_cancel]
  rw [hQ0, Polynomial.coeff_zero, Nat.sub_add_cancel hpos, hmonic.coeff_natDegree, one_mul,
    hcast] at hc
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  apply hK (-P.coeff (n - 1) / n)
  have hmul : (n : K) * (-P.coeff (n - 1) / n) = -P.coeff (n - 1) := mul_div_cancel₀ _ hn0
  have hd := congrArg (fun x : K => x′) hmul
  simp only [Derivation.leibniz, Derivation.map_natCast, smul_eq_mul, mul_zero, add_zero,
    map_neg] at hd
  apply mul_left_cancel₀ hn0
  rw [hd, mul_one]
  linear_combination hc

/-- `diff:rs:lem:tautrans`, the transcendence argument with explicit derivations: `dK` is a
derivation of `K`, `dL` extends it to `L`, and no element of `K` has `dK`-derivative `1`. -/
theorem transcendental_of_derivation_eq_one [CharZero K] (dK : Derivation ℤ K K)
    (dL : Derivation ℤ L L) (hcomm : ∀ k, dL (algebraMap K L k) = algebraMap K L (dK k))
    (hK : ∀ k, dK k ≠ 1) {τ : L} (hτ : dL τ = 1) : Transcendental K τ := by
  letI : Differential K := ⟨dK⟩
  letI : Differential L := ⟨dL⟩
  haveI : DifferentialAlgebra K L := ⟨hcomm⟩
  exact transcendental_of_deriv_eq_one hK hτ

/-- `diff:rs:lem:tautrans` for an arbitrary Hahn field `R((t^Γ))` of characteristic zero and an
arbitrary exponent map: in every differential field extension of `(R((t^Γ)), ∂_T)`, a
primitive `τ` of `1` is transcendental over `R((t^Γ))`. -/
theorem transcendental_of_euler {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] {R : Type*} [Field R] [CharZero R] (φ : Γ →+ R)
    [Algebra (HahnSeries Γ R) L] (D : Derivation ℤ L L)
    (hD : ∀ f, D (algebraMap (HahnSeries Γ R) L f) = algebraMap (HahnSeries Γ R) L (euler φ f))
    {τ : L} (hτ : D τ = 1) : Transcendental (HahnSeries Γ R) τ := by
  haveI : CharZero (HahnSeries Γ R) := charZero_of_injective_ringHom (f := C) C_injective
  exact transcendental_of_derivation_eq_one ((euler φ).restrictScalars ℤ) D hD
    (euler_ne_one φ) hτ

end Transcendence

section Real

/-- The exponent map `γ ↦ (γ : ℂ)` of the real-exponent Hahn field `K_ℝ = ℂ((t^ℝ))`. -/
def realExponent : ℝ →+ ℂ := Complex.ofRealHom.toAddMonoidHom

@[simp]
theorem realExponent_apply (γ : ℝ) : realExponent γ = γ := rfl

theorem realExponent_eq_zero {γ : ℝ} (h : realExponent γ = 0) : γ = 0 :=
  Complex.ofReal_eq_zero.1 h

/-- The Euler derivation `∂_T` of `K_ℝ = ℂ((t^ℝ))`, defined by its coefficient formula
`diff:rs:eq:eulerhahn`. It models the surreal `∂_T = -ω ∂` of `diff:rs:eq:euler` on `K_ℝ`; the
identification with the surreal derivation is pending. -/
def derT : Derivation ℂ (HahnSeries ℝ ℂ) (HahnSeries ℝ ℂ) := euler realExponent

/-- `diff:rs:eq:eulerhahn` on `K_ℝ`: `∂_T (∑ c_γ t^γ) = ∑ γ c_γ t^γ`. This holds by the
definition of `derT`. -/
theorem coeff_derT (f : HahnSeries ℝ ℂ) (γ : ℝ) : (derT f).coeff γ = γ * f.coeff γ := rfl

/-- `∂_T t^a = a t^a`. -/
theorem derT_single (a : ℝ) (c : ℂ) : derT (single a c) = single a (a * c) :=
  euler_single _ a c

/-- The Euler derivation `∂_T` of `K_Γ = ℂ((t^Γ))` for an additive subgroup `Γ ⊆ ℝ`, defined by
its coefficient formula `diff:rs:eq:eulerhahn`. -/
def derTOn (Γ : AddSubgroup ℝ) : Derivation ℂ (HahnSeries Γ ℂ) (HahnSeries Γ ℂ) :=
  euler (realExponent.comp Γ.subtype)

/-- `diff:rs:eq:eulerhahn` on `K_Γ`; this holds by the definition of `derTOn`. -/
theorem coeff_derTOn (Γ : AddSubgroup ℝ) (f : HahnSeries Γ ℂ) (γ : Γ) :
    (derTOn Γ f).coeff γ = ((γ : ℝ) : ℂ) * f.coeff γ := rfl

/-- `diff:rs:lem:euler`, stability and the formula: for every additive subgroup `Γ ⊆ ℝ` the
Euler derivation of `K_ℝ` maps the copy of `K_Γ = ℂ((t^Γ))` into itself and restricts there to
the Euler derivation of `K_Γ`. -/
theorem derT_subgroupEmb (Γ : AddSubgroup ℝ) (f : HahnSeries Γ ℂ) :
    derT (subgroupEmb Γ f) = subgroupEmb Γ (derTOn Γ f) :=
  euler_subgroupEmb _ Γ f

/-- `diff:rs:lem:euler`, stability: `∂_T` preserves every `K_Γ ⊆ K_ℝ`, with no hypothesis
on the subgroup `Γ`. -/
theorem derT_mem_hahnSubfield (Γ : AddSubgroup ℝ) {f : HahnSeries ℝ ℂ}
    (hf : f ∈ hahnSubfield Γ) : derT f ∈ hahnSubfield Γ := by
  rw [mem_hahnSubfield_iff] at hf ⊢
  exact (support_euler_subset _ f).trans (Set.sdiff_subset.trans hf)

/-- `diff:rs:lem:euler`, constants: the constants of `∂_T` in `K_Γ` are exactly `ℂ`. -/
theorem derTOn_eq_zero_iff (Γ : AddSubgroup ℝ) (f : HahnSeries Γ ℂ) :
    derTOn Γ f = 0 ↔ ∃ c : ℂ, C c = f :=
  euler_eq_zero_iff_exists (fun _ h => Subtype.ext (realExponent_eq_zero h)) f

/-- `diff:rs:lem:euler`, constants, in the ambient field `K_ℝ`: the constants of `∂_T` are
exactly `ℂ`. -/
theorem derT_eq_zero_iff (f : HahnSeries ℝ ℂ) : derT f = 0 ↔ ∃ c : ℂ, C c = f :=
  euler_eq_zero_iff_exists (fun _ h => realExponent_eq_zero h) f

/-- `diff:rs:lem:euler`, valuation: `∂_T` maps `K_Γ^{≥0}` into `K_Γ^{>0}`. -/
theorem zero_lt_orderTop_derTOn (Γ : AddSubgroup ℝ) {f : HahnSeries Γ ℂ}
    (hf : 0 ≤ f.orderTop) : 0 < (derTOn Γ f).orderTop :=
  zero_lt_orderTop_euler _ hf

/-- `diff:rs:lem:euler`, valuation, in `K_ℝ`. -/
theorem zero_lt_orderTop_derT {f : HahnSeries ℝ ℂ} (hf : 0 ≤ f.orderTop) :
    0 < (derT f).orderTop :=
  zero_lt_orderTop_euler _ hf

/-- The rescaled derivation `∂ = -t ∂_T` of `K_ℝ`, defined from `derT` by the relation of
`diff:rs:eq:euler`. It models the surreal `∂` on `K_ℝ`; the identification is pending. -/
def der : Derivation ℂ (HahnSeries ℝ ℂ) (HahnSeries ℝ ℂ) := intrinsic realExponent 1

theorem der_apply (f : HahnSeries ℝ ℂ) : der f = -single 1 1 * derT f := rfl

/-- The real-power rule `∂ t^a = -a t^{a+1}` used in the proof of `diff:rs:lem:euler`. Here it
follows from the definitions of `der` and `derT`; it is not derived from the surreal
derivation. -/
theorem der_single (a : ℝ) (c : ℂ) : der (single a c) = single (a + 1) (-(a * c)) := by
  rw [der, intrinsic_single, realExponent_apply, add_comm]

/-- `diff:rs:lem:euler`, the corrected criterion: `∂ = -t ∂_T` preserves `K_Γ ⊆ K_ℝ` exactly
when `Γ = {0}` or `1 ∈ Γ`. -/
theorem der_mem_hahnSubfield_iff (Γ : AddSubgroup ℝ) :
    (∀ f ∈ hahnSubfield Γ, der f ∈ hahnSubfield Γ) ↔ Γ = ⊥ ∨ (1 : ℝ) ∈ Γ := by
  rw [← intrinsic_mem_hahnSubring_iff (R := ℂ) (fun _ h => realExponent_eq_zero h) Γ 1]
  simp only [mem_hahnSubfield_iff, mem_hahnSubring_iff]
  rfl

/-- `diff:rs:lem:tautrans`, first clause, for the Hahn-field model: no element of `K_ℝ` has
`derT`-derivative `1`. -/
theorem derT_ne_one (f : HahnSeries ℝ ℂ) : derT f ≠ 1 :=
  euler_ne_one _ f

/-- `diff:rs:lem:tautrans`, second clause, for the Hahn-field model: in every differential field
extension `L` of `(K_ℝ, ∂_T)`, an element `τ` with `∂_T τ = 1` is transcendental over `K_ℝ`.
This applies to `τ = log t` in `No[i]` once `No[i]` is supplied as such an extension with
`∂_T log t = 1`; that is pending. -/
theorem transcendental_tau {L : Type*} [Field L] [Algebra (HahnSeries ℝ ℂ) L]
    (D : Derivation ℤ L L)
    (hD : ∀ f, D (algebraMap (HahnSeries ℝ ℂ) L f) = algebraMap (HahnSeries ℝ ℂ) L (derT f))
    {τ : L} (hτ : D τ = 1) : Transcendental (HahnSeries ℝ ℂ) τ :=
  transcendental_of_euler realExponent D hD hτ

end Real

end

end Surreal.EulerDerivation
