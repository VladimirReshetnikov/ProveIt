import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Tactic.LinearCombination
import Surreal.HahnSeries.CoefficientMapping
import Surreal.HahnSeries.InfiniteProducts
import Surreal.HahnSeries.RowColumnFinite

/-!
# Coherent diagonal resolvents

This file formalizes the diagonal and scalar parts of `ihs:rf:thm:resolvent` of
`docs/surcomplex/infinite-dimensional-hahn-spectral-theory/article.tex` (Part II), together with
the coherent diagonal algebra `𝒟 = (k^I)((t^Γ))` of `ihs:rf:eq:diagalg` and its embedding into
`𝒜_rf = RCF_I(k)((t^Γ))` of `Surreal.RowColumnFinite`.

Throughout, `k` is an arbitrary field (the source's `ℂ`), `Γ` an arbitrary ordered abelian group
(no divisibility), and `I` an arbitrary index type.

* The coherence lemma singled out in `ihs:rf:sec:formalization`
  (`isPWO_iUnion_support_inv_sub`): if `λᵢ = dᵢ + Δᵢ` with pairwise distinct constants `dᵢ`
  and a common well-ordered positive support for the `Δᵢ`, then for every `z ∈ K = k((t^Γ))`
  the inverses `(λᵢ - z)⁻¹` have a common well-ordered support. The proof follows the source's
  three cases `v(z) < 0`, residue `c ∉ {dᵢ}`, and `c = dⱼ` for exactly one `j`. The hypothesis
  `z ≠ λᵢ` is not needed for this support statement (an absent inverse is `0`).
* The coherent diagonal algebra (`ihs:rf:eq:diagalg`): `(I → k)⟦Γ⟧`, with diagonal entries
  `component i` (ring homomorphisms `componentHom i`). A family `(aᵢ)` of scalar series is the
  diagonal of an element exactly when `⋃ supp aᵢ` is partially well-ordered
  (`exists_component_eq_iff`, `diag`), and an element is a unit exactly when all its entries are
  nonzero and their inverses are coherent (`isUnit_iff_component`).
* The spectrum in `𝒟` (`isUnit_sub_scalar_iff`): for `Λ = D + Δ ∈ 𝒟` with distinct `dᵢ` and
  positive support of `Δ`, `Λ - z` is invertible in `𝒟` iff `z ≠ λᵢ` for all `i`, and then
  its inverse is `diag((λᵢ - z)⁻¹)` (`inverse_sub_scalar_eq_diag`).
* The inclusion `𝒟 ⊆ 𝒜_rf` (`embed`, a ring homomorphism `embedHom`, injective by
  `embed_injective`), by the diagonal matrices `diagHom d` in every coefficient; it sends the
  scalar `z · Id` of `𝒟` to the `K`-algebra scalar `z` of `𝒜_rf` (`embed_scalar`). Its image
  is exactly the set of elements of `𝒜_rf` all of whose coefficients are diagonal matrices
  (`mem_range_embed_iff`). For a commutative ring `k`, `R_I` is given the ring structure
  `instRingRcf := Algebra.semiringToRing k`, extending the semiring structure of
  `Surreal.RowColumnFinite` (instance search does not find `Subalgebra.toRing` for `rcf k I`),
  so that `A - z` and `σ_{𝒜rf}` make sense. Its negation is `(-1 : k) • F`, which agrees with
  the negation of `Subalgebra.toRing` only propositionally, not definitionally.
* The transfer to `𝒜_rf` (`spectrum_eq_range`, `inverse_sub_algebraMap_eq`): whenever
  `A ∈ 𝒜_rf` is diagonalized as `AV = VΛ` by an invertible `V ∈ 𝒜_rf` with `Λ` as above,
  then `σ_{𝒜rf}(A) = {λᵢ : i ∈ I}` (Mathlib's `spectrum` for the `K`-algebra `𝒜_rf`, which is
  exactly the source's `ihs:rf:def:spectrum`), and for `z` outside it
  `(A - z)⁻¹ = V diag((λᵢ - z)⁻¹) V⁻¹`. This is the non-Hermitian form of the theorem; the
  unitary form `(A - z)⁻¹ = U diag((λᵢ - z)⁻¹) U*` is `spectrum_eq_range_of_unitary` and
  `inverse_sub_algebraMap_eq_of_unitary`. Reality of the `dᵢ` and self-adjointness are not
  used, as the source remarks. The eigenvalue direction uses that the matrix unit `E_{jj}` is a
  nonzero element killed by `Λ - λⱼ`, the operator form of the source's eigenvector argument.

Pending: the existence of the diagonalizer, i.e. `ihs:rf:thm:similarity` and
`ihs:rf:thm:unitary`, is not formalized; here it is a hypothesis (`AV = VΛ` with `V`
invertible, respectively `U` unitary). Consequently the theorem is proved for the actual
`A = D + B` of the source only once that diagonalizer is supplied. `ihs:rf:cor:forcing` is not
formalized. Nor are the remarks after `ihs:rf:eq:diagalg` (`𝒟 = K^I` for finite `I` or trivial
`Γ`, strict inclusion for infinite `I` and `Γ ≠ 0`, and the absence of an ordinary bound on a
fixed coefficient), the example `Q = diag(t^{nη})` before the theorem (only the unit criterion
`isUnit_iff_component` in `𝒟` is proved, not the non-invertibility of `Q` in `𝒜_rf`), and the
example `ihs:rf:ex:accum`.
-/

namespace Surreal.DiagonalResolvent

open _root_.HahnSeries
open Surreal.HahnSeries (orderTop_pos_of_support_pos support_pos_of_orderTop_pos
  support_inv_one_sub_subset isPWO_closure_of_pos mapCoefficients support_mapCoefficients_subset
  orderTop_le_mapCoefficients)
open Surreal.RowColumnFinite (rcf entry_apply coordProj coordProj_ne_zero)
open scoped Pointwise

noncomputable section

section Coherence

variable {Γ k : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-- The support of the inverse of `a · y · (1 - q)`, for a constant `a` and a `q` supported in a
set `T` of positive exponents, lies in `supp y⁻¹ + ⟨T⟩`. -/
theorem support_inv_C_mul_mul_one_sub_subset (a : k) (y q : k⟦Γ⟧) {T : Set Γ}
    (hq : q.support ⊆ T) (hT : ∀ g ∈ T, 0 < g) :
    ((C a * y * (1 - q))⁻¹).support ⊆ (y⁻¹).support + (AddSubmonoid.closure T : Set Γ) := by
  have hq' : 0 < q.orderTop := orderTop_pos_of_support_pos fun g hg => hT g (hq hg)
  rw [mul_inv, mul_inv, ← map_inv₀ (C : k →+* k⟦Γ⟧) a, C_mul_eq_smul]
  intro g hg
  obtain ⟨x, hx, w, hw, rfl⟩ := support_mul_subset hg
  exact ⟨x, support_smul_subset _ _ hx, w,
    AddSubmonoid.closure_mono hq (support_inv_one_sub_subset hq' hw), rfl⟩

/-- The support of `c + x`, for a constant `c`, lies in `{0} ∪ supp x`. -/
theorem support_C_add_subset (c : k) (x : k⟦Γ⟧) :
    (C c + x).support ⊆ insert 0 x.support := by
  intro g hg
  rcases support_add_subset (C c) x hg with h | h
  · rw [C_apply] at h
    exact Or.inl (Set.mem_singleton_iff.mp (support_single_subset h))
  · exact Or.inr h

/-- The coherence lemma of `ihs:rf:thm:resolvent` (the separate lemma flagged in
`ihs:rf:sec:formalization`): if `λᵢ = dᵢ + Δᵢ` with pairwise distinct constants `dᵢ` and a common
well-ordered positive support for the `Δᵢ`, then for every `z` the inverses `(λᵢ - z)⁻¹` have a
common well-ordered support. -/
theorem isPWO_iUnion_support_inv_sub {I : Type*} (d : I → k) (hd : Function.Injective d)
    (Δ : I → k⟦Γ⟧) (hΔ : (⋃ i, (Δ i).support).IsPWO) (hpos : ∀ i, 0 < (Δ i).orderTop)
    (z : k⟦Γ⟧) : (⋃ i, ((C (d i) + Δ i - z)⁻¹).support).IsPWO := by
  have hSpos : ∀ g ∈ ⋃ i, (Δ i).support, 0 < g := fun g hg => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    exact support_pos_of_orderTop_pos (hpos i) g hi
  rcases lt_or_ge z.order 0 with hneg | hnn
  · -- `v(z) < 0`: `λᵢ - z = -z (1 - z⁻¹ λᵢ)`.
    have hz0 : z ≠ 0 := fun h => by
      rw [h, order_zero] at hneg
      exact lt_irrefl _ hneg
    have hord : z.order + z⁻¹.order = 0 := by
      rw [← order_mul hz0 (inv_ne_zero hz0), mul_inv_cancel₀ hz0, order_one]
    have hinv : ∀ g ∈ (z⁻¹).support, 0 < g := fun g hg => by
      have h1 : z⁻¹.order ≤ g := order_le_of_coeff_ne_zero ((mem_support _ _).mp hg)
      rw [eq_neg_of_add_eq_zero_right hord] at h1
      exact (neg_pos.mpr hneg).trans_le h1
    set T : Set Γ := (z⁻¹).support + insert 0 (⋃ i, (Δ i).support) with hT
    have hTpos : ∀ g ∈ T, 0 < g := by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      have hy0 : 0 ≤ y := by
        rcases hy with rfl | hy
        · exact le_rfl
        · exact (hSpos y hy).le
      exact add_pos_of_pos_of_nonneg (hinv x hx) hy0
    have hTpwo : T.IsPWO := z⁻¹.isPWO_support.add (hΔ.insert 0)
    refine (z⁻¹.isPWO_support.add (isPWO_closure_of_pos hTpwo hTpos)).mono
      (Set.iUnion_subset fun i => ?_)
    have hfac : C (d i) + Δ i - z = C (-1) * z * (1 - z⁻¹ * (C (d i) + Δ i)) := by
      have h1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
      rw [map_neg, map_one]
      linear_combination -(C (d i) + Δ i) * h1
    rw [hfac]
    refine support_inv_C_mul_mul_one_sub_subset _ _ _ (fun g hg => ?_) hTpos
    obtain ⟨x, hx, y, hy, rfl⟩ := support_mul_subset hg
    refine ⟨x, hx, y, ?_, rfl⟩
    rcases support_C_add_subset (d i) (Δ i) hy with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i, h⟩)
  · -- `v(z) ≥ 0`: write `z = c + ζ` with `c = z.coeff 0` and `ζ` of positive support.
    set c := z.coeff 0 with hc
    set ζ := z - C c with hζdef
    have hζ : ∀ g ∈ ζ.support, 0 < g := by
      intro g hg
      rw [mem_support, hζdef, coeff_sub, C_apply] at hg
      by_cases hg0 : g = 0
      · rw [hg0, coeff_single_same, ← hc, sub_self] at hg
        exact absurd rfl hg
      · rw [coeff_single_of_ne hg0, sub_zero] at hg
        exact lt_of_le_of_ne (hnn.trans (order_le_of_coeff_ne_zero hg)) (Ne.symm hg0)
    set T : Set Γ := (⋃ i, (Δ i).support) ∪ ζ.support with hT
    have hTpos : ∀ g ∈ T, 0 < g := by
      rintro g (hg | hg)
      · exact hSpos g hg
      · exact hζ g hg
    have hTpwo : T.IsPWO := hΔ.union ζ.isPWO_support
    have hA : ((1 : k⟦Γ⟧)⁻¹.support + (AddSubmonoid.closure T : Set Γ)).IsPWO :=
      (1 : k⟦Γ⟧)⁻¹.isPWO_support.add (isPWO_closure_of_pos hTpwo hTpos)
    have key : ∀ i, d i ≠ c → ((C (d i) + Δ i - z)⁻¹).support ⊆
        (1 : k⟦Γ⟧)⁻¹.support + (AddSubmonoid.closure T : Set Γ) := by
      intro i hi
      have hfac : C (d i) + Δ i - z =
          C (d i - c) * 1 * (1 - -(C (d i - c)⁻¹ * (Δ i - ζ))) := by
        have h1 : C (d i - c) * C (d i - c)⁻¹ = (1 : k⟦Γ⟧) := by
          rw [← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr hi), map_one]
        have h2 : C (d i - c) = C (d i) - (C c : k⟦Γ⟧) := map_sub _ _ _
        rw [hζdef]
        linear_combination (-1 : k⟦Γ⟧) * h2 - (Δ i - (z - C c)) * h1
      rw [hfac]
      refine support_inv_C_mul_mul_one_sub_subset _ _ _ (fun g hg => ?_) hTpos
      rw [support_neg, C_mul_eq_smul] at hg
      rcases support_sub_subset _ _ (support_smul_subset _ _ hg) with h | h
      · exact Or.inl (Set.mem_iUnion.mpr ⟨i, h⟩)
      · exact Or.inr h
    by_cases hj : ∃ j, d j = c
    · obtain ⟨j, hj⟩ := hj
      refine (hA.union ((C (d j) + Δ j - z)⁻¹).isPWO_support).mono
        (Set.iUnion_subset fun i => ?_)
      by_cases hij : i = j
      · subst hij
        exact Set.subset_union_right
      · exact (key i fun h => hij (hd (h.trans hj.symm))).trans Set.subset_union_left
    · exact hA.mono (Set.iUnion_subset fun i => key i fun h => hj ⟨i, h⟩)

end Coherence

section Components

variable {Γ k I : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing k]

/-- The `i`-th diagonal entry `𝒟 → K` of `𝒟 = (k^I)((t^Γ))`, as a ring homomorphism. -/
def componentHom (i : I) : (I → k)⟦Γ⟧ →+* k⟦Γ⟧ :=
  mapCoefficients (Pi.evalRingHom (fun _ => k) i)

/-- The `i`-th diagonal entry of an element of the coherent diagonal algebra
`𝒟 = (k^I)((t^Γ))`. -/
def component (i : I) (X : (I → k)⟦Γ⟧) : k⟦Γ⟧ :=
  componentHom (Γ := Γ) (k := k) i X

theorem componentHom_apply (i : I) (X : (I → k)⟦Γ⟧) :
    componentHom (Γ := Γ) (k := k) i X = component i X := rfl

@[simp] theorem coeff_component (i : I) (X : (I → k)⟦Γ⟧) (g : Γ) :
    (component i X).coeff g = X.coeff g i := rfl

@[simp] theorem component_sub (i : I) (X Y : (I → k)⟦Γ⟧) :
    component i (X - Y) = component i X - component i Y :=
  map_sub (componentHom (Γ := Γ) (k := k) i) X Y

@[simp] theorem component_mul (i : I) (X Y : (I → k)⟦Γ⟧) :
    component i (X * Y) = component i X * component i Y :=
  map_mul (componentHom (Γ := Γ) (k := k) i) X Y

@[simp] theorem component_one (i : I) : component i (1 : (I → k)⟦Γ⟧) = 1 :=
  map_one (componentHom (Γ := Γ) (k := k) i)

theorem support_component_subset (i : I) (X : (I → k)⟦Γ⟧) :
    (component i X).support ⊆ X.support :=
  support_mapCoefficients_subset _ X

theorem orderTop_le_orderTop_component (i : I) (X : (I → k)⟦Γ⟧) :
    X.orderTop ≤ (component i X).orderTop :=
  orderTop_le_mapCoefficients _ X

/-- The support of an element of `𝒟` is the union of the supports of its entries. -/
theorem iUnion_support_component (X : (I → k)⟦Γ⟧) :
    ⋃ i, (component i X).support = X.support := by
  refine subset_antisymm (Set.iUnion_subset fun i => support_component_subset i X)
    fun g hg => ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ((mem_support _ _).mp hg)
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- An element of `𝒟` is determined by its diagonal entries. -/
theorem ext_component {X Y : (I → k)⟦Γ⟧} (h : ∀ i, component i X = component i Y) : X = Y :=
  _root_.HahnSeries.ext (funext fun g => funext fun i =>
    congrArg (fun x : k⟦Γ⟧ => x.coeff g) (h i))

/-- `ihs:rf:eq:diagalg`: a coherent family `(aᵢ)` of scalar series, i.e. one whose supports have a
partially well-ordered union, as an element of `𝒟 = (k^I)((t^Γ))`. -/
def diag (a : I → k⟦Γ⟧) (ha : (⋃ i, (a i).support).IsPWO) : (I → k)⟦Γ⟧ where
  coeff g i := (a i).coeff g
  isPWO_support' := ha.mono fun g hg => by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (Function.mem_support.mp hg)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

@[simp] theorem component_diag (a : I → k⟦Γ⟧) (ha : (⋃ i, (a i).support).IsPWO) (i : I) :
    component i (diag a ha) = a i := rfl

/-- `ihs:rf:eq:diagalg`: a family of scalar series is the diagonal of an element of `𝒟` exactly
when the union of its supports is partially well-ordered (well-ordered, as `Γ` is linear). -/
theorem exists_component_eq_iff (a : I → k⟦Γ⟧) :
    (∃ X : (I → k)⟦Γ⟧, ∀ i, component i X = a i) ↔ (⋃ i, (a i).support).IsPWO := by
  constructor
  · rintro ⟨X, hX⟩
    rw [← funext hX, iUnion_support_component]
    exact X.isPWO_support
  · intro ha
    exact ⟨diag a ha, component_diag a ha⟩

/-- The scalar `z · Id` of `𝒟`, for `z ∈ K`. -/
def scalar (z : k⟦Γ⟧) : (I → k)⟦Γ⟧ :=
  mapCoefficients (Γ := Γ) (Pi.constRingHom I k) z

@[simp] theorem component_scalar (i : I) (z : k⟦Γ⟧) : component i (scalar z : (I → k)⟦Γ⟧) = z :=
  rfl

@[simp] theorem component_C (i : I) (d : I → k) : component i (C d : (I → k)⟦Γ⟧) = C (d i) :=
  map_C d (Pi.evalRingHom (fun _ => k) i)

end Components

section DiagonalSpectrum

variable {Γ k I : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-- Units of the coherent diagonal algebra: `X ∈ 𝒟` is invertible exactly when every entry is
nonzero and the entrywise inverses are coherent. -/
theorem isUnit_iff_component (X : (I → k)⟦Γ⟧) :
    IsUnit X ↔ (∀ i, component i X ≠ 0) ∧ (⋃ i, ((component i X)⁻¹).support).IsPWO := by
  constructor
  · intro hX
    refine ⟨fun i => (hX.map (componentHom (Γ := Γ) (k := k) i)).ne_zero, ?_⟩
    obtain ⟨u, rfl⟩ := hX
    refine ((u⁻¹ : ((I → k)⟦Γ⟧)ˣ) : (I → k)⟦Γ⟧).isPWO_support.mono
      (Set.iUnion_subset fun i => ?_)
    have hinv : component i ((u⁻¹ : ((I → k)⟦Γ⟧)ˣ) : (I → k)⟦Γ⟧) = (component i u)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by rw [← component_mul, Units.mul_inv, component_one])
    rw [← hinv]
    exact support_component_subset i _
  · rintro ⟨h0, hpwo⟩
    refine IsUnit.of_mul_eq_one (diag _ hpwo) (ext_component fun i => ?_)
    rw [component_mul, component_diag, component_one, mul_inv_cancel₀ (h0 i)]

/-- The entries of the inverse of a unit of `𝒟` are the inverses of its entries. -/
theorem component_inverse {X : (I → k)⟦Γ⟧} (hX : IsUnit X) (i : I) :
    component i (Ring.inverse X) = (component i X)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← component_mul, Ring.mul_inverse_cancel X hX, component_one])

/-- The coherence lemma for `Λ = D + Δ ∈ 𝒟` with distinct `dᵢ` and positive support of `Δ`: the
entrywise inverses `(λᵢ - z)⁻¹` are coherent for every `z ∈ K`. -/
theorem isPWO_iUnion_support_inv_component_sub (Λ : (I → k)⟦Γ⟧) {d : I → k}
    (hd : Function.Injective d) (hΛ : 0 < (Λ - C d).orderTop) (z : k⟦Γ⟧) :
    (⋃ i, ((component i Λ - z)⁻¹).support).IsPWO := by
  have h := isPWO_iUnion_support_inv_sub d hd (fun i => component i (Λ - C d))
    ((Λ - C d).isPWO_support.mono (Set.iUnion_subset fun i => support_component_subset i _))
    (fun i => hΛ.trans_le (orderTop_le_orderTop_component i _)) z
  simpa only [component_sub, component_C, add_sub_cancel] using h

/-- `ihs:rf:thm:resolvent` in the coherent diagonal algebra: for `Λ = D + Δ ∈ 𝒟` with pairwise
distinct constants `dᵢ` and `supp Δ ⊆ Γ_{>0}`, `Λ - z` is invertible in `𝒟` exactly when `z` is
none of the diagonal entries `λᵢ`. -/
theorem isUnit_sub_scalar_iff (Λ : (I → k)⟦Γ⟧) {d : I → k} (hd : Function.Injective d)
    (hΛ : 0 < (Λ - C d).orderTop) (z : k⟦Γ⟧) :
    IsUnit (Λ - scalar z) ↔ ∀ i, component i Λ ≠ z := by
  rw [isUnit_iff_component]
  simp only [component_sub, component_scalar, ne_eq, sub_eq_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, isPWO_iUnion_support_inv_component_sub Λ hd hΛ z⟩⟩

/-- `ihs:rf:thm:resolvent` in the coherent diagonal algebra: the inverse of `Λ - z` is the
coherent diagonal `diag((λᵢ - z)⁻¹)`. -/
theorem inverse_sub_scalar_eq_diag (Λ : (I → k)⟦Γ⟧) {d : I → k} (hd : Function.Injective d)
    (hΛ : 0 < (Λ - C d).orderTop) {z : k⟦Γ⟧} (hz : ∀ i, component i Λ ≠ z) :
    Ring.inverse (Λ - scalar z) =
      diag (fun i => (component i Λ - z)⁻¹) (isPWO_iUnion_support_inv_component_sub Λ hd hΛ z) :=
  ext_component fun i => by
    rw [component_inverse ((isUnit_sub_scalar_iff Λ hd hΛ z).2 hz), component_diag,
      component_sub, component_scalar]

end DiagonalSpectrum

section Embedding

variable {k I : Type*} [CommRing k]

/-- For a commutative ring `k`, `R_I = RCF_I(k)` is a ring, so that `𝒜_rf = R_I((t^Γ))` is a ring
and `A - z` and the spectrum `σ_{𝒜rf}` make sense. This is `Algebra.semiringToRing k`, extending
the semiring structure of `rcf k I`; its negation is `(-1 : k) • F`, equal to the negation of
`Subalgebra.toRing` only propositionally, so it should be the only ring structure used on
`rcf k I`. -/
instance instRingRcf : Ring (rcf k I) :=
  Algebra.semiringToRing k

/-- The diagonal endomorphism `x ↦ (dᵢ xᵢ)ᵢ` of `k^(I)`, for an arbitrary family `d`. -/
def diagEnd (d : I → k) : Module.End k (I →₀ k) where
  toFun x := Finsupp.ofSupportFinite (fun i => d i * x i)
    (Set.Finite.subset x.hasFiniteSupport fun _ hi => right_ne_zero_of_mul hi)
  map_add' x y := Finsupp.ext fun i => mul_add (d i) (x i) (y i)
  map_smul' c x := Finsupp.ext fun i => mul_left_comm (d i) c (x i)

theorem diagEnd_apply (d : I → k) (x : I →₀ k) (i : I) : diagEnd d x i = d i * x i := rfl

theorem diagEnd_mem (d : I → k) : diagEnd d ∈ rcf k I := fun i =>
  (Set.finite_singleton i).subset fun j hj => by
    by_contra h
    apply hj
    rw [entry_apply, diagEnd_apply, Finsupp.single_eq_of_ne (Ne.symm h), mul_zero]

/-- Diagonal matrices as a ring homomorphism `k^I → R_I = RCF_I(k)`: every diagonal matrix is
row- and column-finite, however large its entries. -/
def diagHom : (I → k) →+* rcf k I where
  toFun d := ⟨diagEnd d, diagEnd_mem d⟩
  map_one' := Subtype.ext (LinearMap.ext fun x => Finsupp.ext fun i => one_mul (x i))
  map_mul' d e := Subtype.ext (LinearMap.ext fun x => Finsupp.ext fun i =>
    mul_assoc (d i) (e i) (x i))
  map_zero' := Subtype.ext (LinearMap.ext fun x => Finsupp.ext fun i => zero_mul (x i))
  map_add' d e := Subtype.ext (LinearMap.ext fun x => Finsupp.ext fun i =>
    add_mul (d i) (e i) (x i))

theorem diagHom_apply (d : I → k) (x : I →₀ k) (i : I) :
    ((diagHom (k := k) (I := I) d : rcf k I) : Module.End k (I →₀ k)) x i = d i * x i := rfl

theorem diagHom_injective : Function.Injective (diagHom (k := k) (I := I)) := by
  intro d e h
  funext i
  have := congrArg (fun F : rcf k I => (F : Module.End k (I →₀ k)) (Finsupp.single i 1) i) h
  simpa only [diagHom_apply, Finsupp.single_eq_same, mul_one] using this

variable {Γ : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- The inclusion `𝒟 = (k^I)((t^Γ)) → 𝒜_rf = RCF_I(k)((t^Γ))` of `ihs:rf:eq:diagalg`, by
diagonal matrices in every coefficient. -/
def embed (X : (I → k)⟦Γ⟧) : (rcf k I)⟦Γ⟧ :=
  X.map (diagHom (k := k) (I := I))

/-- The inclusion `𝒟 → 𝒜_rf` as a ring homomorphism. -/
def embedHom : (I → k)⟦Γ⟧ →+* (rcf k I)⟦Γ⟧ where
  toFun := embed
  map_zero' := _root_.HahnSeries.map_zero (diagHom (k := k) (I := I)).toZeroHom
  map_one' := _root_.HahnSeries.map_one (diagHom (k := k) (I := I)).toMonoidWithZeroHom
  map_add' _ _ := _root_.HahnSeries.map_add (diagHom (k := k) (I := I)).toAddMonoidHom
  map_mul' _ _ := _root_.HahnSeries.map_mul (diagHom (k := k) (I := I)).toNonUnitalRingHom

theorem embedHom_apply (X : (I → k)⟦Γ⟧) : embedHom (Γ := Γ) (k := k) (I := I) X = embed X := rfl

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
@[simp] theorem coeff_embed (X : (I → k)⟦Γ⟧) (g : Γ) :
    (embed X).coeff g = diagHom (k := k) (I := I) (X.coeff g) := rfl

theorem embed_sub (X Y : (I → k)⟦Γ⟧) : embed (X - Y) = embed X - embed Y :=
  map_sub (embedHom (Γ := Γ) (k := k) (I := I)) X Y

theorem embed_mul (X Y : (I → k)⟦Γ⟧) : embed (X * Y) = embed X * embed Y :=
  map_mul (embedHom (Γ := Γ) (k := k) (I := I)) X Y

theorem embed_one : embed (1 : (I → k)⟦Γ⟧) = 1 :=
  map_one (embedHom (Γ := Γ) (k := k) (I := I))

theorem isUnit_embed {X : (I → k)⟦Γ⟧} (hX : IsUnit X) : IsUnit (embed X) :=
  hX.map (embedHom (Γ := Γ) (k := k) (I := I))

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- `ihs:rf:eq:diagalg`: the inclusion `𝒟 ⊆ 𝒜_rf` is injective. -/
theorem embed_injective : Function.Injective (embed : (I → k)⟦Γ⟧ → (rcf k I)⟦Γ⟧) :=
  fun _ _ h => _root_.HahnSeries.ext (funext fun g =>
    diagHom_injective (congrArg (fun Z : (rcf k I)⟦Γ⟧ => Z.coeff g) h))

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- `ihs:rf:eq:diagalg`: the image of the inclusion `𝒟 → 𝒜_rf` consists exactly of the elements
of `𝒜_rf` all of whose coefficients are diagonal matrices. -/
theorem mem_range_embed_iff (F : (rcf k I)⟦Γ⟧) :
    F ∈ Set.range (embed : (I → k)⟦Γ⟧ → (rcf k I)⟦Γ⟧) ↔
      ∀ g, F.coeff g ∈ Set.range (diagHom (k := k) (I := I)) := by
  constructor
  · rintro ⟨X, rfl⟩ g
    exact ⟨X.coeff g, rfl⟩
  · intro h
    choose d hd using h
    refine ⟨⟨d, F.isPWO_support.mono fun g hg => ?_⟩, _root_.HahnSeries.ext (funext hd)⟩
    rw [mem_support]
    intro hF
    apply Function.mem_support.mp hg
    apply diagHom_injective
    rw [hd g, hF, map_zero]

end Embedding

section Transfer

variable {Γ k I : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field k]

/-- The scalar `z · Id` of `𝒟` is the `K`-algebra scalar `z` of `𝒜_rf`. -/
theorem embed_scalar (z : k⟦Γ⟧) :
    embed (scalar z : (I → k)⟦Γ⟧) = algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ z :=
  _root_.HahnSeries.ext (funext fun _ => Subtype.ext (LinearMap.ext fun _ => Finsupp.ext
    fun _ => rfl))

/-- A diagonal operator with a vanishing entry `j` kills the matrix unit `E_{jj}`. -/
theorem embed_mul_C_coordProj {X : (I → k)⟦Γ⟧} {j : I} (hj : component j X = 0) :
    embed X * C (coordProj j) = 0 := by
  refine _root_.HahnSeries.ext (funext fun g => ?_)
  rw [C_apply, coeff_mul_single_zero, coeff_embed, _root_.HahnSeries.coeff_zero]
  refine Subtype.ext (LinearMap.ext fun x => Finsupp.ext fun i => ?_)
  change X.coeff g i * (Finsupp.single j (x j)) i = 0
  by_cases hij : i = j
  · subst hij
    have h : X.coeff g i = 0 := congrArg (fun y : k⟦Γ⟧ => y.coeff g) hj
    rw [h, zero_mul]
  · rw [Finsupp.single_eq_of_ne hij, mul_zero]

/-- If `AV = VΛ` with `V` invertible, then `A - z = V (Λ - z) V⁻¹`. -/
theorem sub_algebraMap_eq_conj {A V : (rcf k I)⟦Γ⟧} (hV : IsUnit V) {Λ : (I → k)⟦Γ⟧}
    (hAV : A * V = V * embed Λ) (z : k⟦Γ⟧) :
    A - algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ z = V * embed (Λ - scalar z) * Ring.inverse V := by
  rw [embed_sub, embed_scalar, mul_sub, sub_mul, ← hAV, ← Algebra.commutes,
    Ring.mul_inverse_cancel_right V A hV, Ring.mul_inverse_cancel_right V _ hV]

/-- `ihs:rf:thm:resolvent`, invertibility: if `A ∈ 𝒜_rf` satisfies `AV = VΛ` for an invertible
`V ∈ 𝒜_rf` and `Λ = D + Δ ∈ 𝒟` with pairwise distinct `dᵢ` and positive support of `Δ`, then
`A - z` is invertible in `𝒜_rf` exactly when `z` is none of the `λᵢ`. -/
theorem isUnit_sub_algebraMap_iff {A V : (rcf k I)⟦Γ⟧} (hV : IsUnit V) {Λ : (I → k)⟦Γ⟧}
    (hAV : A * V = V * embed Λ) {d : I → k} (hd : Function.Injective d)
    (hΛ : 0 < (Λ - C d).orderTop) (z : k⟦Γ⟧) :
    IsUnit (A - algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ z) ↔ ∀ i, component i Λ ≠ z := by
  obtain ⟨u, rfl⟩ := hV
  rw [sub_algebraMap_eq_conj u.isUnit hAV z, Ring.inverse_unit, Units.isUnit_mul_units,
    Units.isUnit_units_mul]
  constructor
  · intro h i hi
    have h0 : embed (Λ - scalar z) * C (coordProj i) = 0 :=
      embed_mul_C_coordProj (by rw [component_sub, component_scalar, hi, sub_self])
    exact C_ne_zero (coordProj_ne_zero i) (h.mul_right_eq_zero.mp h0)
  · intro h
    exact isUnit_embed ((isUnit_sub_scalar_iff Λ hd hΛ z).2 h)

/-- `ihs:rf:thm:resolvent`, `ihs:rf:eq:spectrum` (simple-complex-residue form): under the
hypotheses of `isUnit_sub_algebraMap_iff`, `σ_{𝒜rf}(A) = {λᵢ : i ∈ I}`. -/
theorem spectrum_eq_range {A V : (rcf k I)⟦Γ⟧} (hV : IsUnit V) {Λ : (I → k)⟦Γ⟧}
    (hAV : A * V = V * embed Λ) {d : I → k} (hd : Function.Injective d)
    (hΛ : 0 < (Λ - C d).orderTop) :
    spectrum k⟦Γ⟧ A = Set.range fun i => component i Λ := by
  ext z
  rw [spectrum.mem_iff, ← IsUnit.neg_iff, neg_sub, isUnit_sub_algebraMap_iff hV hAV hd hΛ z]
  simp only [ne_eq, not_forall, not_not, Set.mem_range]

/-- The inclusion `𝒟 → 𝒜_rf` commutes with inverses of units. -/
theorem inverse_embed {X : (I → k)⟦Γ⟧} (hX : IsUnit X) :
    Ring.inverse (embed X : (rcf k I)⟦Γ⟧) = embed (Ring.inverse X) := by
  have h := (Ring.inverse_mul_eq_iff_eq_mul (embed X : (rcf k I)⟦Γ⟧) 1 (embed (Ring.inverse X))
    (isUnit_embed hX)).2 (by rw [← embed_mul, Ring.mul_inverse_cancel X hX, embed_one])
  rwa [mul_one] at h

/-- `ihs:rf:thm:resolvent`, `ihs:rf:eq:resolvent` (simple-complex-residue form): under the
hypotheses of `isUnit_sub_algebraMap_iff`, for `z` outside `{λᵢ}`,
`(A - z)⁻¹ = V diag((λᵢ - z)⁻¹) V⁻¹ ∈ 𝒜_rf`. -/
theorem inverse_sub_algebraMap_eq {A V : (rcf k I)⟦Γ⟧} (hV : IsUnit V) {Λ : (I → k)⟦Γ⟧}
    (hAV : A * V = V * embed Λ) {d : I → k} (hd : Function.Injective d)
    (hΛ : 0 < (Λ - C d).orderTop) {z : k⟦Γ⟧} (hz : ∀ i, component i Λ ≠ z) :
    Ring.inverse (A - algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ z) =
      V * embed (diag (fun i => (component i Λ - z)⁻¹)
        (isPWO_iUnion_support_inv_component_sub Λ hd hΛ z)) * Ring.inverse V := by
  have hY := (isUnit_sub_scalar_iff Λ hd hΛ z).2 hz
  rw [← inverse_sub_scalar_eq_diag Λ hd hΛ hz, ← inverse_embed hY,
    sub_algebraMap_eq_conj hV hAV z, Ring.inverse_mul (Or.inr hV.ringInverse),
    Ring.inverse_mul (Or.inl hV), Ring.inverse_inverse hV, mul_assoc]

section Unitary

variable [StarRing k]

/-- `ihs:rf:thm:resolvent`, `ihs:rf:eq:spectrum` (unitary form): if `AU = UΛ` with
`U*U = UU* = Id` and `Λ = D + Δ ∈ 𝒟` with pairwise distinct `dᵢ` and positive support of `Δ`, then
`σ_{𝒜rf}(A) = {λᵢ : i ∈ I}`. -/
theorem spectrum_eq_range_of_unitary {A U : (rcf k I)⟦Γ⟧} (hU : star U * U = 1)
    (hU' : U * star U = 1) {Λ : (I → k)⟦Γ⟧} (hAU : A * U = U * embed Λ) {d : I → k}
    (hd : Function.Injective d) (hΛ : 0 < (Λ - C d).orderTop) :
    spectrum k⟦Γ⟧ A = Set.range fun i => component i Λ :=
  spectrum_eq_range ⟨⟨U, star U, hU', hU⟩, rfl⟩ hAU hd hΛ

/-- `ihs:rf:thm:resolvent`, `ihs:rf:eq:resolvent` (unitary form): under the hypotheses of
`spectrum_eq_range_of_unitary`, for `z` outside `{λᵢ}`,
`(A - z)⁻¹ = U diag((λᵢ - z)⁻¹) U* ∈ 𝒜_rf`. -/
theorem inverse_sub_algebraMap_eq_of_unitary {A U : (rcf k I)⟦Γ⟧} (hU : star U * U = 1)
    (hU' : U * star U = 1) {Λ : (I → k)⟦Γ⟧} (hAU : A * U = U * embed Λ) {d : I → k}
    (hd : Function.Injective d) (hΛ : 0 < (Λ - C d).orderTop) {z : k⟦Γ⟧}
    (hz : ∀ i, component i Λ ≠ z) :
    Ring.inverse (A - algebraMap k⟦Γ⟧ (rcf k I)⟦Γ⟧ z) =
      U * embed (diag (fun i => (component i Λ - z)⁻¹)
        (isPWO_iUnion_support_inv_component_sub Λ hd hΛ z)) * star U := by
  have h := inverse_sub_algebraMap_eq ⟨⟨U, star U, hU', hU⟩, rfl⟩ hAU hd hΛ hz
  rwa [show Ring.inverse U = star U from Ring.inverse_unit ⟨U, star U, hU', hU⟩] at h

end Unitary

end Transfer

end

end Surreal.DiagonalResolvent
