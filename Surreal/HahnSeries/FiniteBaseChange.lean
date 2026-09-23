import Surreal.HahnSeries.CoefficientMapping
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Finite base change commutes with Hahn series

This module proves `tail:lem:basechange` (report
`docs/surreal/tail-spans-and-differential-transcendence`). Let `F / M` be a finite coefficient
extension with basis `u_1, …, u_e`. The coefficientwise embedding
`M((t^Γ)) → F((t^Γ))` makes `F((t^Γ))` an `M((t^Γ))`-algebra, and constants `F → F((t^Γ))`
provide the second factor of the common coefficient extension.

* `hahnBasis`, `hahnBasis_apply`, `hahnBasis_repr`: the same `u_j`, viewed as constants, form a
  basis of `F((t^Γ))` over `M((t^Γ))`. The coordinates are the coefficientwise coordinates
  (`coordinate`), and every coordinate series has support inside `supp f`
  (`support_coordinate_subset`). Hence every `f` is `∑ j, u_j f_j` for exactly one family
  `f_j ∈ M((t^Γ))`, and that family has `supp f_j ⊆ supp f` (`existsUnique_sum_C_mul`,
  `eq_coordinate_of_sum_eq`).
* `span_range_C_eq_top`, `range_sup_range_C_eq_top`, `fieldRange_sup_fieldRange_C_eq_top`:
  `F((t^Γ)) = M((t^Γ))F`, both as the `M((t^Γ))`-span of the constants and as the compositum
  (for rings and for fields) of the images of `M((t^Γ))` and `F` in `F((t^Γ))`.
* `finrank_hahn_eq_card`, `finrank_hahn`: `[F((t^Γ)) : M((t^Γ))] = [F : M] = e`.
* `hahnAut`, `hahnAutHom`, `hahnAutHom_injective`: coefficient automorphisms act
  coefficientwise, preserve supports, fix `M((t^Γ))`, and give an injective group
  homomorphism `Aut(F/M) → Aut(F((t^Γ))/M((t^Γ)))`.
* `hahnAutHom_bijective`, `hahnGaloisEquiv`, `isGalois_hahn`: if `F / M` is finite Galois, this
  homomorphism is a group isomorphism onto the full automorphism group, and
  `F((t^Γ)) / M((t^Γ))` is itself Galois.

The algebra and linear-algebra statements hold for an arbitrary commutative ring `M` and a
commutative `M`-algebra `F` with a finite basis, and an arbitrary linearly ordered cancellative
exponent monoid `Γ` (the degree statements `finrank_hahn_eq_card` and `finrank_hahn` also need
`M` nontrivial). The Galois-group isomorphism needs fields `M`, `F`; the Galois property of
the base-changed extension needs `Γ` to be a group (so that the Hahn series form fields).

The source's "common coefficient extension" is read as `F((t^Γ))` itself, containing the image
of `M((t^Γ))` and the constants `F`. To place everything inside a larger `L((t^Γ))` (for
example with `L` an algebraic closure of `M`), the fact needed is that an injective coefficient
map `F → L` induces an injective ring map `F((t^Γ)) → L((t^Γ))`; this is
`mapCoefficients_injective`.

The `M((t^Γ))`-algebra structure `hahnBaseChangeAlgebra` is deliberately not a global instance
(for `F = M` it would compete with `Algebra.id`); it is a local instance here. It parallels
`Surreal.RowColumnFinite.hahnAlgebra`, which allows a noncommutative coefficient algebra and is
built from `RowColumnFinite.hahnMap`; here `F` is commutative and the map is `mapCoefficients`.
The two are separate structures, so a file should not activate both as instances. The warning
`tail:warn:infinitebase` about infinite algebraic extensions is not part of this lemma.
-/

namespace Surreal.FiniteBaseChange

open _root_.HahnSeries Module
open Surreal.HahnSeries (mapCoefficients coeff_mapCoefficients support_mapCoefficients_subset)

noncomputable section

section CommRing

variable {Γ M F ι : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing M] [CommRing F] [Algebra M F]

/-- The coefficientwise embedding `M((t^Γ)) → F((t^Γ))`, as an algebra structure. It is used as
a local instance only. -/
abbrev hahnBaseChangeAlgebra : Algebra M⟦Γ⟧ F⟦Γ⟧ :=
  (mapCoefficients (algebraMap M F)).toAlgebra

attribute [local instance] hahnBaseChangeAlgebra

theorem algebraMap_hahn_apply (c : M⟦Γ⟧) :
    algebraMap M⟦Γ⟧ F⟦Γ⟧ c = mapCoefficients (algebraMap M F) c := rfl

theorem smul_hahn_def (c : M⟦Γ⟧) (f : F⟦Γ⟧) :
    c • f = mapCoefficients (algebraMap M F) c * f := rfl

/-- An injective coefficient map `φ : F → L` induces an injective ring map
`F((t^Γ)) → L((t^Γ))`. This transports `F((t^Γ))` into any larger coefficient extension. -/
theorem mapCoefficients_injective {L : Type*} [CommRing L] {φ : F →+* L}
    (hφ : Function.Injective φ) : Function.Injective (mapCoefficients (Γ := Γ) φ) := by
  intro x y hxy
  ext γ
  apply hφ
  have hγ := congrArg (fun z : L⟦Γ⟧ => z.coeff γ) hxy
  simpa using hγ

/-- The coefficientwise embedding `M((t^Γ)) → F((t^Γ))` is injective whenever `M → F` is
(for instance for a field extension), so both `M((t^Γ))` and `F` sit inside `F((t^Γ))`. -/
theorem algebraMap_hahn_injective (h : Function.Injective (algebraMap M F)) :
    Function.Injective (algebraMap M⟦Γ⟧ F⟦Γ⟧) :=
  mapCoefficients_injective h

/-- The `i`th coordinate series of `f`: the `i`th basis coordinate of every coefficient. -/
def coordinate (b : Basis ι M F) (i : ι) (f : F⟦Γ⟧) : M⟦Γ⟧ :=
  f.map (b.coord i)

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
@[simp] theorem coeff_coordinate (b : Basis ι M F) (i : ι) (f : F⟦Γ⟧) (γ : Γ) :
    (coordinate b i f).coeff γ = b.repr (f.coeff γ) i := rfl

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
/-- `tail:lem:basechange`, support clause: every coordinate series is supported in `supp f`. -/
theorem support_coordinate_subset (b : Basis ι M F) (i : ι) (f : F⟦Γ⟧) :
    (coordinate b i f).support ⊆ f.support := by
  intro γ hγ
  rw [mem_support] at hγ ⊢
  intro h
  apply hγ
  rw [coeff_coordinate, h, map_zero, Finsupp.zero_apply]

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem coordinate_add (b : Basis ι M F) (i : ι) (f g : F⟦Γ⟧) :
    coordinate b i (f + g) = coordinate b i f + coordinate b i g := by
  ext γ
  rw [coeff_coordinate, coeff_add, coeff_add, map_add, Finsupp.add_apply, coeff_coordinate,
    coeff_coordinate]

/-- Coordinates are `M((t^Γ))`-linear: convolution commutes with coefficientwise coordinates. -/
theorem coordinate_smul (b : Basis ι M F) (i : ι) (c : M⟦Γ⟧) (f : F⟦Γ⟧) :
    coordinate b i (c • f) = c * coordinate b i f := by
  ext γ
  rw [smul_hahn_def, coeff_coordinate,
    coeff_mul_left' c.isPWO_support (support_mapCoefficients_subset _ c),
    coeff_mul_right' f.isPWO_support (support_coordinate_subset b i f), map_sum,
    Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [coeff_mapCoefficients, coeff_coordinate, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
    smul_eq_mul]

variable [Fintype ι]

/-- Recombine coordinate series with the constant basis vectors: `∑ j, u_j f_j`. -/
def recombine (b : Basis ι M F) (g : ι → M⟦Γ⟧) : F⟦Γ⟧ :=
  ∑ i, C (b i) * mapCoefficients (algebraMap M F) (g i)

theorem coeff_recombine (b : Basis ι M F) (g : ι → M⟦Γ⟧) (γ : Γ) :
    (recombine b g).coeff γ = ∑ i, (g i).coeff γ • b i := by
  rw [recombine, coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C_mul_eq_smul, coeff_smul, coeff_mapCoefficients, smul_eq_mul, Algebra.smul_def, mul_comm]

@[simp] theorem coordinate_recombine (b : Basis ι M F) (g : ι → M⟦Γ⟧) (i : ι) :
    coordinate b i (recombine b g) = g i := by
  ext γ
  rw [coeff_coordinate, coeff_recombine, b.repr_sum_self]

/-- `tail:lem:basechange`, existence: `f = ∑ j, u_j f_j` with the coordinate series `f_j`. -/
@[simp] theorem recombine_coordinate (b : Basis ι M F) (f : F⟦Γ⟧) :
    recombine b (fun i => coordinate b i f) = f := by
  ext γ
  rw [coeff_recombine]
  simp only [coeff_coordinate]
  exact b.sum_repr _

/-- The coordinate isomorphism `F((t^Γ)) ≃ M((t^Γ))^e` over `M((t^Γ))`. -/
def coordinateEquiv (b : Basis ι M F) : F⟦Γ⟧ ≃ₗ[M⟦Γ⟧] (ι → M⟦Γ⟧) where
  toFun f i := coordinate b i f
  invFun := recombine b
  map_add' f g := funext fun i => coordinate_add b i f g
  map_smul' c f := funext fun i => coordinate_smul b i c f
  left_inv := recombine_coordinate b
  right_inv g := funext fun i => coordinate_recombine b g i

/-- `tail:lem:basechange`, basis clause: the basis of `F((t^Γ))` over `M((t^Γ))` obtained by
Hahn base change of a finite basis of `F` over `M`. -/
def hahnBasis (b : Basis ι M F) : Basis ι M⟦Γ⟧ F⟦Γ⟧ :=
  .ofEquivFun (coordinateEquiv b)

@[simp] theorem hahnBasis_repr (b : Basis ι M F) (f : F⟦Γ⟧) (i : ι) :
    (hahnBasis b).repr f i = coordinate b i f := rfl

/-- `tail:lem:basechange`: the Hahn base-change basis consists of the same vectors `u_j`,
viewed as constant series. -/
@[simp] theorem hahnBasis_apply (b : Basis ι M F) (i : ι) :
    hahnBasis (Γ := Γ) b i = C (b i) := by
  classical
  rw [hahnBasis, Basis.coe_ofEquivFun]
  change recombine b (Pi.single i 1) = C (b i)
  rw [recombine, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, map_one, mul_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, map_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coe_hahnBasis (b : Basis ι M F) :
    ⇑(hahnBasis (Γ := Γ) b) = fun i => C (b i) :=
  funext (hahnBasis_apply b)

/-- `tail:lem:basechange`, uniqueness: a representation `f = ∑ j, u_j f_j` with
`f_j ∈ M((t^Γ))` is the coordinate representation. -/
theorem eq_coordinate_of_sum_eq (b : Basis ι M F) {f : F⟦Γ⟧} {g : ι → M⟦Γ⟧}
    (h : ∑ i, C (b i) * mapCoefficients (algebraMap M F) (g i) = f) :
    g = fun i => coordinate b i f := by
  funext i
  rw [← h, ← recombine, coordinate_recombine]

/-- `tail:lem:basechange`, basis clause: every `f ∈ F((t^Γ))` is `∑ j, u_j f_j` for exactly
one family `f_j ∈ M((t^Γ))` (uniqueness among all families, with no support condition), and
every such representation has `supp f_j ⊆ supp f` for every `j`. -/
theorem existsUnique_sum_C_mul (b : Basis ι M F) (f : F⟦Γ⟧) :
    (∃! g : ι → M⟦Γ⟧, ∑ i, C (b i) * mapCoefficients (algebraMap M F) (g i) = f) ∧
      ∀ g : ι → M⟦Γ⟧, ∑ i, C (b i) * mapCoefficients (algebraMap M F) (g i) = f →
        ∀ i, (g i).support ⊆ f.support := by
  refine ⟨⟨fun i => coordinate b i f, recombine_coordinate b f,
    fun _ hg => eq_coordinate_of_sum_eq b hg⟩, fun g hg i => ?_⟩
  rw [congrFun (eq_coordinate_of_sum_eq b hg) i]
  exact support_coordinate_subset b i f

/-- The constant basis vectors span `F((t^Γ))` over `M((t^Γ))`. -/
theorem span_range_C_basis_eq_top (b : Basis ι M F) :
    Submodule.span M⟦Γ⟧ (Set.range fun i => (C (b i) : F⟦Γ⟧)) = ⊤ := by
  rw [← coe_hahnBasis]
  exact (hahnBasis b).span_eq

variable (Γ M F) in
/-- `tail:lem:basechange`, `F((t^Γ)) = M((t^Γ))F`: the constants `F` span `F((t^Γ))` over
`M((t^Γ))`. -/
theorem span_range_C_eq_top [Module.Free M F] [Module.Finite M F] :
    Submodule.span M⟦Γ⟧ (Set.range (C : F → F⟦Γ⟧)) = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← span_range_C_basis_eq_top (Module.Free.chooseBasis M F)]
  exact Submodule.span_mono (Set.range_comp_subset_range _ _)

variable (Γ M F) in
/-- `tail:lem:basechange`, `F((t^Γ)) = M((t^Γ))F` as a compositum of rings: the images of
`M((t^Γ))` (coefficientwise) and of `F` (as constants) in `F((t^Γ))` generate it as a ring. -/
theorem range_sup_range_C_eq_top [Module.Free M F] [Module.Finite M F] :
    (mapCoefficients (Γ := Γ) (algebraMap M F)).range ⊔ (C : F →+* F⟦Γ⟧).range = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  rw [← recombine_coordinate (Module.Free.chooseBasis M F) f, recombine]
  refine Subring.sum_mem _ fun i _ => Subring.mul_mem _ ?_ ?_
  · exact (le_sup_right : (C : F →+* F⟦Γ⟧).range ≤ _) (RingHom.mem_range_self _ _)
  · exact (le_sup_left : (mapCoefficients (Γ := Γ) (algebraMap M F)).range ≤ _)
      (RingHom.mem_range_self _ _)

/-- `tail:lem:basechange`, degree from a basis: `[F((t^Γ)) : M((t^Γ))] = e`. -/
theorem finrank_hahn_eq_card [Nontrivial M] (b : Basis ι M F) :
    finrank M⟦Γ⟧ F⟦Γ⟧ = Fintype.card ι :=
  finrank_eq_card_basis (hahnBasis b)

variable (Γ M F) in
/-- `tail:lem:basechange`, degree: `[F((t^Γ)) : M((t^Γ))] = [F : M]`. -/
theorem finrank_hahn [Nontrivial M] [Module.Free M F] [Module.Finite M F] :
    finrank M⟦Γ⟧ F⟦Γ⟧ = finrank M F := by
  rw [finrank_hahn_eq_card (Module.Free.chooseBasis M F), finrank_eq_card_chooseBasisIndex]

variable (Γ M F) in
/-- If `F` is free and finite over `M`, then `F((t^Γ))` is free over `M((t^Γ))`. -/
theorem free_hahn [Module.Free M F] [Module.Finite M F] : Module.Free M⟦Γ⟧ F⟦Γ⟧ :=
  .of_basis (hahnBasis (Module.Free.chooseBasis M F))

variable (Γ M F) in
/-- If `F` is free and finite over `M`, then `F((t^Γ))` is finite over `M((t^Γ))`. -/
theorem finite_hahn [Module.Free M F] [Module.Finite M F] : Module.Finite M⟦Γ⟧ F⟦Γ⟧ :=
  .of_basis (hahnBasis (Module.Free.chooseBasis M F))

end CommRing

section Automorphisms

variable {Γ M F : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing M] [CommRing F] [Algebra M F]

attribute [local instance] hahnBaseChangeAlgebra

/-- `tail:lem:basechange`: an `M`-automorphism of `F` acts coefficientwise on `F((t^Γ))`, as an
automorphism fixing `M((t^Γ))`. -/
def hahnAut (σ : F ≃ₐ[M] F) : F⟦Γ⟧ ≃ₐ[M⟦Γ⟧] F⟦Γ⟧ where
  toFun := mapCoefficients (σ : F →+* F)
  invFun := mapCoefficients (σ.symm : F →+* F)
  left_inv f := by
    ext γ
    simp
  right_inv f := by
    ext γ
    simp
  map_mul' := map_mul _
  map_add' := map_add _
  commutes' c := by
    ext γ
    simp [algebraMap_hahn_apply]

@[simp] theorem coeff_hahnAut (σ : F ≃ₐ[M] F) (f : F⟦Γ⟧) (γ : Γ) :
    (hahnAut σ f).coeff γ = σ (f.coeff γ) := rfl

/-- Coefficient automorphisms preserve supports. -/
@[simp] theorem support_hahnAut (σ : F ≃ₐ[M] F) (f : F⟦Γ⟧) :
    (hahnAut σ f).support = f.support := by
  ext γ
  simp

@[simp] theorem hahnAut_C (σ : F ≃ₐ[M] F) (x : F) :
    hahnAut (Γ := Γ) σ (C x) = C (σ x) := by
  ext γ
  by_cases h : γ = 0 <;> simp [h]

variable (Γ M F) in
/-- The coefficientwise action as a group homomorphism `Aut(F/M) → Aut(F((t^Γ))/M((t^Γ)))`. -/
def hahnAutHom : (F ≃ₐ[M] F) →* (F⟦Γ⟧ ≃ₐ[M⟦Γ⟧] F⟦Γ⟧) where
  toFun := hahnAut
  map_one' := by
    ext f γ
    simp
  map_mul' σ τ := by
    ext f γ
    simp

@[simp] theorem hahnAutHom_apply (σ : F ≃ₐ[M] F) : hahnAutHom Γ M F σ = hahnAut σ := rfl

/-- Distinct coefficient automorphisms give distinct automorphisms of the Hahn extension. -/
theorem hahnAutHom_injective : Function.Injective (hahnAutHom Γ M F) := by
  intro σ τ h
  ext x
  have hx := congrArg (fun φ : F⟦Γ⟧ ≃ₐ[M⟦Γ⟧] F⟦Γ⟧ => (φ (C x)).coeff 0) h
  simpa using hx

end Automorphisms

section Galois

variable {Γ M F : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [Field M] [Field F] [Algebra M F]

attribute [local instance] hahnBaseChangeAlgebra

/-- `tail:lem:basechange`, Galois clause: for a finite Galois extension `F / M`, the
coefficientwise action exhausts the automorphism group of `F((t^Γ)) / M((t^Γ))`. -/
theorem hahnAutHom_bijective [FiniteDimensional M F] [IsGalois M F] :
    Function.Bijective (hahnAutHom Γ M F) := by
  haveI := free_hahn Γ M F
  haveI := finite_hahn Γ M F
  refine hahnAutHom_injective.bijective_of_nat_card_le ?_
  calc Nat.card (F⟦Γ⟧ ≃ₐ[M⟦Γ⟧] F⟦Γ⟧) ≤ Nat.card (F⟦Γ⟧ →ₐ[M⟦Γ⟧] F⟦Γ⟧) :=
        Nat.card_le_card_of_injective _ AlgEquiv.coe_toAlgHom_injective
    _ ≤ finrank M⟦Γ⟧ F⟦Γ⟧ := card_algHom_le_finrank _ _ _
    _ = finrank M F := finrank_hahn Γ M F
    _ = Nat.card (F ≃ₐ[M] F) := (IsGalois.card_aut_eq_finrank M F).symm

variable (Γ M F) in
/-- `tail:lem:basechange`, Galois clause: `Gal(F/M) ≃ Aut(F((t^Γ))/M((t^Γ)))`, acting
coefficientwise. -/
def hahnGaloisEquiv [FiniteDimensional M F] [IsGalois M F] :
    (F ≃ₐ[M] F) ≃* (F⟦Γ⟧ ≃ₐ[M⟦Γ⟧] F⟦Γ⟧) :=
  MulEquiv.ofBijective (hahnAutHom Γ M F) hahnAutHom_bijective

@[simp] theorem hahnGaloisEquiv_apply [FiniteDimensional M F] [IsGalois M F]
    (σ : F ≃ₐ[M] F) : hahnGaloisEquiv Γ M F σ = hahnAut σ := rfl

end Galois

section GaloisField

variable {Γ M F : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field M] [Field F] [Algebra M F]

attribute [local instance] hahnBaseChangeAlgebra

variable (Γ M F) in
/-- `tail:lem:basechange`, `F((t^Γ)) = M((t^Γ))F` as a compositum of fields. -/
theorem fieldRange_sup_fieldRange_C_eq_top [FiniteDimensional M F] :
    (mapCoefficients (Γ := Γ) (algebraMap M F)).fieldRange ⊔ (C : F →+* F⟦Γ⟧).fieldRange =
      ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  rw [← recombine_coordinate (Module.Free.chooseBasis M F) f, recombine]
  refine Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ ?_ ?_
  · exact (le_sup_right : (C : F →+* F⟦Γ⟧).fieldRange ≤ _) (RingHom.mem_fieldRange_self _ _)
  · exact (le_sup_left : (mapCoefficients (Γ := Γ) (algebraMap M F)).fieldRange ≤ _)
      (RingHom.mem_fieldRange_self _ _)

variable (Γ M F) in
/-- `tail:lem:basechange`, Galois clause: if `F / M` is finite Galois, so is the Hahn
base change `F((t^Γ)) / M((t^Γ))`. -/
theorem isGalois_hahn [FiniteDimensional M F] [IsGalois M F] : IsGalois M⟦Γ⟧ F⟦Γ⟧ := by
  haveI := finite_hahn Γ M F
  refine IsGalois.of_card_aut_eq_finrank _ _ ?_
  rw [finrank_hahn Γ M F, ← IsGalois.card_aut_eq_finrank M F]
  exact (Nat.card_eq_of_bijective _ hahnAutHom_bijective).symm

end GaloisField

end

end Surreal.FiniteBaseChange
