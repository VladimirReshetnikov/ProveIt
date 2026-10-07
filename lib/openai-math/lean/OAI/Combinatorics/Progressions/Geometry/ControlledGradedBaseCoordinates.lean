/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationBaseGrading

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [fintypeSigma : Fintype σ]

noncomputable def weightedBaseLinear (w : σ → ℕ) (d : ℕ) :
    weightedSubalgebra w d →ₗ[ℚ] (σ → ℚ) :=
  baseLinear.comp (weightedSubalgebra w d).subtype

@[simp] theorem weightedBaseLinear_apply (w : σ → ℕ) (d : ℕ)
    (x : weightedSubalgebra w d) : weightedBaseLinear w d x = x.val.base := rfl

theorem base_gradeProjection (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (j : ℕ) (x : weightedSubalgebra w d) :
    weightedBaseLinear w d
      (basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j x) =
      basisGradeProjection (Pi.basisFun ℚ σ) w j (weightedBaseLinear w d x) := by
  funext i
  rw [weightedBaseLinear_apply, weightedBasis_projection_base]
  have h := basisGradeProjection_repr (Pi.basisFun ℚ σ) w j x.val.base i
  simpa only [Pi.basisFun_repr, weightedBaseLinear_apply] using h.symm

theorem basisGradedSubmodule_base_image (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (weightedSubalgebra w d))
    (hU : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U) :
    BasisGradedSubmodule (Pi.basisFun ℚ σ) w (U.map (weightedBaseLinear w d)) := by
  intro j b hb
  obtain ⟨x, hx, rfl⟩ := hb
  exact ⟨_, hU j x hx, base_gradeProjection w d hw j x⟩

theorem basisGradedSubmodule_ambient_base_image (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype)) :
    BasisGradedSubmodule (Pi.basisFun ℚ σ) w (U.map baseLinear) := by
  intro j b hb
  obtain ⟨x, hx, rfl⟩ := hb
  let y : weightedSubalgebra w d := ⟨x, hU hx⟩
  let z := basisGradeProjection (weightedBasis w d hw) (weightedBasisGrade w d) j y
  have hz : z.val ∈ U := hgraded j y hx
  refine ⟨z.val, hz, ?_⟩
  exact base_gradeProjection w d hw j y

noncomputable def submoduleBasisCoordinates {τ : Type*} [Fintype τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) : (τ → ℚ) →ₗ[ℚ] (σ → ℚ) :=
  K.subtype.comp b.equivFun.symm.toLinearMap

omit fintypeSigma in
theorem submoduleBasisCoordinates_injective [Fintype σ] {τ : Type*} [Fintype τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) :
    Function.Injective (submoduleBasisCoordinates K b) :=
  Subtype.val_injective.comp b.equivFun.symm.injective

omit fintypeSigma in
@[simp] theorem submoduleBasisCoordinates_range [Fintype σ] {τ : Type*} [Fintype τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) :
    (submoduleBasisCoordinates K b).range = K := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (b.equivFun.symm z).property
  · intro hx
    refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
    change (b.equivFun.symm (b.equivFun ⟨x, hx⟩)).val = x
    rw [b.equivFun.symm_apply_apply]

omit fintypeSigma in
@[simp] theorem submoduleBasisCoordinates_single [Fintype σ] {τ : Type*}
    [Fintype τ] [DecidableEq τ]
    (K : Submodule ℚ (σ → ℚ)) (b : Basis τ ℚ K) (j : τ) :
    submoduleBasisCoordinates K b (Pi.single j 1) = (b j).val := by
  change (b.equivFun.symm (Pi.single j 1)).val = _
  rw [b.equivFun_symm_apply]
  simp [Pi.single_apply]

theorem exists_graded_base_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (K : Submodule ℚ (σ → ℚ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℚ σ) w K) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (A : (Fin n → ℚ) →ₗ[ℚ] (σ → ℚ)),
      n ≤ Fintype.card σ ∧ (∀ j, 0 < v j) ∧ (∀ j, v j ≤ d) ∧
      Function.Injective A ∧ A.range = K ∧
      ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0 := by
  obtain ⟨n, v, b, hv, hvd, hb⟩ :=
    exists_basisGraded_coordinate_basis_bounded w K hK hw hwd
  refine ⟨n, v, submoduleBasisCoordinates K b, ?_, hv, hvd,
    submoduleBasisCoordinates_injective K b, submoduleBasisCoordinates_range K b, ?_⟩
  · have hn : Module.finrank ℚ K = n := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
    rw [← hn]
    simpa only [Module.finrank_pi] using Submodule.finrank_le K
  · intro j i hji
    rw [submoduleBasisCoordinates_single]
    exact hb j i hji

theorem exists_weighted_translation_base_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (U : Submodule ℚ (weightedSubalgebra w d))
    (hU : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d) U) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (A : (Fin n → ℚ) →ₗ[ℚ] (σ → ℚ)),
      n ≤ Fintype.card σ ∧ (∀ j, 0 < v j) ∧ (∀ j, v j ≤ d) ∧
      Function.Injective A ∧ A.range = U.map (weightedBaseLinear w d) ∧
      ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0 :=
  exists_graded_base_coordinates w d hw hwd _ (basisGradedSubmodule_base_image w d hw U hU)

theorem exists_ambient_translation_base_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (U : Submodule ℚ (PolynomialTranslationLie σ))
    (hU : U ≤ (weightedSubalgebra w d).toSubmodule)
    (hgraded : BasisGradedSubmodule (weightedBasis w d hw) (weightedBasisGrade w d)
      (U.comap (weightedSubalgebra w d).subtype)) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (A : (Fin n → ℚ) →ₗ[ℚ] (σ → ℚ)),
      n ≤ Fintype.card σ ∧ (∀ j, 0 < v j) ∧ (∀ j, v j ≤ d) ∧
      Function.Injective A ∧ A.range = U.map baseLinear ∧
      ∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0 :=
  exists_graded_base_coordinates w d hw hwd _
    (basisGradedSubmodule_ambient_base_image w d hw U hU hgraded)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module
open scoped BigOperators

variable {σ J : Type*} [Fintype σ]

theorem exists_controlled_basisGraded_coordinate_basis (w : σ → ℕ)
    (K : Submodule ℚ (σ → ℚ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℚ σ) w K)
    (g : J → (σ → ℚ)) (hspan : Submodule.span ℚ (Set.range g) = K)
    {H : ℕ} (hH : 1 ≤ H) (hentries : ∀ j i, RationalHeightLE (g j i) H) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (b : Basis (Fin n) ℚ K),
      (∀ j, v j ∈ Set.range w) ∧
      (∀ j i, v j ≠ w i → (b j).val i = 0) ∧
      (∀ j i, RationalHeightLE ((b j).val i) H) ∧
      ∀ j, ∃ a : J, (b j).val =
        basisGradeProjection (Pi.basisFun ℚ σ) w (v j) (g a) := by
  classical
  have hgm : ∀ a, g a ∈ K := by
    intro a
    rw [← hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  let S : Set K := {x | ∃ a : J, ∃ j ∈ Set.range w,
    x.val = basisGradeProjection (Pi.basisFun ℚ σ) w j (g a)}
  have hspanK : Submodule.span ℚ (Set.range (fun a => (⟨g a, hgm a⟩ : K))) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff K hgm).mpr hspan
  have hS : ⊤ ≤ Submodule.span ℚ S := by
    rw [← hspanK]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    let y (j : ℕ) : K := ⟨basisGradeProjection (Pi.basisFun ℚ σ) w j (g a),
      hK j (g a) (hgm a)⟩
    have hsum : ∑ j ∈ Finset.univ.image w, y j = (⟨g a, hgm a⟩ : K) := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using sum_basisGradeProjection_pi w (g a)
    change (⟨g a, hgm a⟩ : K) ∈ Submodule.span ℚ S
    rw [← hsum]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.subset_span
    refine ⟨a, j, ?_, rfl⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    exact ⟨i, hi⟩
  let B := Basis.ofSpan hS
  let := FiniteDimensional.fintypeBasisIndex B
  let b := B.reindex (Fintype.equivFin _)
  have hb : ∀ j, b j ∈ S := by
    intro j
    dsimp only [b]
    rw [Basis.reindex_apply]
    exact Basis.ofSpan_subset hS ⟨_, rfl⟩
  choose a v hv hproj using hb
  refine ⟨_, v, b, hv, ?_, ?_, fun j => ⟨a j, hproj j⟩⟩
  · intro j i hji
    rw [hproj j, basisGradeProjection_pi_apply, ite_eq_right (Ne.symm hji)]
  · intro j i
    rw [hproj j, basisGradeProjection_pi_apply]
    split_ifs
    · exact hentries (a j) i
    · simpa [RationalHeightLE] using hH

namespace PolynomialTranslationLie

theorem exists_controlled_graded_base_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (K : Submodule ℚ (σ → ℚ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℚ σ) w K)
    (g : J → (σ → ℚ)) (hspan : Submodule.span ℚ (Set.range g) = K)
    {H : ℕ} (hH : 1 ≤ H) (hentries : ∀ j i, RationalHeightLE (g j i) H) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (A : (Fin n → ℚ) →ₗ[ℚ] (σ → ℚ)),
      n ≤ Fintype.card σ ∧ (∀ j, 0 < v j) ∧ (∀ j, v j ≤ d) ∧
      Function.Injective A ∧ A.range = K ∧
      (∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0) ∧
      (∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) ∧
      ∀ j, ∃ a : J, A (Pi.single j 1) =
        basisGradeProjection (Pi.basisFun ℚ σ) w (v j) (g a) := by
  obtain ⟨n, v, b, hv, hcoord, hheight, hselected⟩ :=
    exists_controlled_basisGraded_coordinate_basis w K hK g hspan hH hentries
  refine ⟨n, v, submoduleBasisCoordinates K b, ?_, ?_, ?_,
    submoduleBasisCoordinates_injective K b, submoduleBasisCoordinates_range K b,
    ?_, ?_, ?_⟩
  · have hn : Module.finrank ℚ K = n := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
    rw [← hn]
    simpa only [Module.finrank_pi] using Submodule.finrank_le K
  · intro j
    obtain ⟨i, hi⟩ := hv j
    simpa only [← hi] using hw i
  · intro j
    obtain ⟨i, hi⟩ := hv j
    simpa only [← hi] using hwd i
  · intro j i hji
    rw [submoduleBasisCoordinates_single]
    exact hcoord j i hji
  · intro j i
    rw [submoduleBasisCoordinates_single]
    exact hheight j i
  · intro j
    rw [submoduleBasisCoordinates_single]
    exact hselected j

end PolynomialTranslationLie

end Erdos3

end

end OAI
