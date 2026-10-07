/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Geometry.GradedTopCoordinates
import OAI.Combinatorics.Progressions.Linear.SplitPreimageSpanning

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

noncomputable def gradedLayerOneProjection : F.AssociatedGraded →ₗ[ℚ] (L ⧸ F.layer 2) :=
  (F.layer 2).mkQ.comp
    (e.repr.symm.toLinearMap.comp (F.associatedGradedBasis e ω hF).repr.toLinearMap)

theorem gradedLayerOneProjection_coordinate (x : F.AssociatedGraded) (i : LayerOneBasisIndex ω) :
    (F.layerOneBasis e ω hF).repr (F.gradedLayerOneProjection e ω hF x) i =
      (F.associatedGradedBasis e ω hF).repr x i.val := by
  change (F.layerOneBasis e ω hF).repr
    ((F.layer 2).mkQ (e.repr.symm ((F.associatedGradedBasis e ω hF).repr x))) i = _
  rw [F.layerOneBasis_repr_mk, LinearEquiv.apply_symm_apply]

theorem layerOneGradedMap_coordinate (x : L ⧸ F.layer 2) (i : LayerOneBasisIndex ω) :
    (F.associatedGradedBasis e ω hF).repr (F.layerOneGradedMap e ω hF x) i.val =
      (F.layerOneBasis e ω hF).repr x i := by
  obtain ⟨v, rfl⟩ := (F.layer 2).mkQ_surjective x
  rw [F.layerOneGradedMap_mk, F.gradedPieceProjection_coordinate, F.layerOneBasis_repr_mk]
  have hpos := F.adaptedBasis_weight_pos e ω hF i.val
  have hnot := i.property
  rw [ite_eq_left (show ω i.val = 1 by omega)]

theorem gradedLayerOneProjection_rightInverse (x : L ⧸ F.layer 2) :
    F.gradedLayerOneProjection e ω hF (F.layerOneGradedMap e ω hF x) = x := by
  apply (F.layerOneBasis e ω hF).repr.injective
  ext i
  rw [F.gradedLayerOneProjection_coordinate, F.layerOneGradedMap_coordinate]

theorem layerOneGradedMap_projection (x : F.AssociatedGraded) :
    F.layerOneGradedMap e ω hF (F.gradedLayerOneProjection e ω hF x) =
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω 1 x := by
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext i
  change (F.associatedGradedBasis e ω hF).repr
    (F.gradedPieceProjection e ω hF 1 (supportedQuotientSection e (F.layer 2) {i | 2 ≤ ω i}
      (hF 2) (F.gradedLayerOneProjection e ω hF x))) i = _
  rw [F.gradedPieceProjection_coordinate, basisGradeProjection_repr]
  by_cases hi : ω i = 1
  · rw [ite_eq_left hi, ite_eq_left hi]
    have hni : ¬2 ≤ ω i := by omega
    rw [supportedQuotientSection_coordinate e (F.layer 2) {i | 2 ≤ ω i}
      (hF 2) _ ⟨i, hni⟩]
    exact F.gradedLayerOneProjection_coordinate e ω hF x ⟨i, hni⟩
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem layerOneGradedSubmodule_eq_image (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule) :
    F.layerOneGradedSubmodule e ω hF U = U.toSubmodule.map (F.gradedLayerOneProjection e ω hF) := by
  ext x
  constructor
  · intro hx
    exact ⟨F.layerOneGradedMap e ω hF x, hx, F.gradedLayerOneProjection_rightInverse e ω hF x⟩
  · rintro ⟨v, hv, rfl⟩
    change F.layerOneGradedMap e ω hF (F.gradedLayerOneProjection e ω hF v) ∈ U
    rw [F.layerOneGradedMap_projection]
    exact hU 1 v hv

theorem gradedLayerOneProjection_spanning (U : LieSubalgebra ℚ F.AssociatedGraded)
    (hU : BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω U.toSubmodule)
    (v : κ → F.AssociatedGraded) (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) :
    Submodule.span ℚ (Set.range (fun j => F.gradedLayerOneProjection e ω hF (v j))) =
      F.layerOneGradedSubmodule e ω hF U := by
  rw [F.layerOneGradedSubmodule_eq_image e ω hF U hU, ← hv, Submodule.map_span, ← Set.range_comp]
  rfl

theorem gradedLayerOneProjection_height (x : F.AssociatedGraded) {H : ℕ}
    (hx : ∀ i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr x i) H) :
    ∀ i, RationalHeightLE ((F.layerOneBasis e ω hF).repr (F.gradedLayerOneProjection e ω hF x) i) H := by
  intro i
  rw [F.gradedLayerOneProjection_coordinate]
  exact hx i.val

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "bG" => F.associatedGradedBasis e ω hF

theorem layerOneGradedMap_injective : Function.Injective (F.layerOneGradedMap e ω hF) := by
  intro x y hxy
  have h := congrArg (F.gradedLayerOneProjection e ω hF) hxy
  simpa only [F.gradedLayerOneProjection_rightInverse] using h

theorem layerOneGradedMap_pure (x : L ⧸ F.layer 2) :
    basisGradeProjection bG ω 1 (F.layerOneGradedMap e ω hF x) = F.layerOneGradedMap e ω hF x := by
  rw [← F.layerOneGradedMap_projection, F.gradedLayerOneProjection_rightInverse]

theorem layerOneGradedMap_coordinate_zero (x : L ⧸ F.layer 2) (i : ι) (hi : ω i ≠ 1) :
    (bG).repr (F.layerOneGradedMap e ω hF x) i = 0 := by
  have h := congrArg (fun y => (bG).repr y i) (F.layerOneGradedMap_pure e ω hF x)
  rw [basisGradeProjection_repr, ite_eq_right hi] at h
  exact h.symm

theorem layerOneGradedMap_height (x : L ⧸ F.layer 2) {H : ℕ} (hH : 1 ≤ H)
    (hx : ∀ i, RationalHeightLE ((F.layerOneBasis e ω hF).repr x i) H) :
    ∀ i, RationalHeightLE ((bG).repr (F.layerOneGradedMap e ω hF x) i) H := by
  intro i
  by_cases hi : ω i = 1
  · have hni : ¬ 2 ≤ ω i := by omega
    rw [F.layerOneGradedMap_coordinate e ω hF x ⟨i, hni⟩]
    exact hx ⟨i, hni⟩
  · rw [F.layerOneGradedMap_coordinate_zero e ω hF x i hi]
    exact rationalHeightLE_zero hH

theorem realLayerOneGradedMap_pure (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    basisGradeProjection ((bG).baseChange ℝ) ω 1 ((F.layerOneGradedMap e ω hF).baseChange ℝ x) =
      (F.layerOneGradedMap e ω hF).baseChange ℝ x := by
  change basisCoordinateProjection ((bG).baseChange ℝ) {i | ω i = 1}
    ((F.layerOneGradedMap e ω hF).baseChange ℝ x) = _
  rw [← basisCoordinateProjection_baseChange]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    exact congrArg (fun y => a ⊗ₜ[ℚ] y) (F.layerOneGradedMap_pure e ω hF x)

noncomputable def gradedHorizontalKernel (K : Submodule ℚ (L ⧸ F.layer 2)) :
    Submodule ℚ F.AssociatedGraded := K.map (F.layerOneGradedMap e ω hF)

noncomputable def gradedHorizontalKernelEquiv (K : Submodule ℚ (L ⧸ F.layer 2)) :
    K ≃ₗ[ℚ] F.gradedHorizontalKernel e ω hF K :=
  Submodule.equivMapOfInjective (F.layerOneGradedMap e ω hF) (F.layerOneGradedMap_injective e ω hF) K

noncomputable def gradedHorizontalKernelBasis (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K) :
    Basis κ ℚ (F.gradedHorizontalKernel e ω hF K) := b.map (F.gradedHorizontalKernelEquiv e ω hF K)

theorem gradedHorizontalKernelBasis_coe (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K) (i : κ) :
    (F.gradedHorizontalKernelBasis e ω hF K b i : F.AssociatedGraded) =
      F.layerOneGradedMap e ω hF (b i : L ⧸ F.layer 2) := by
  rw [gradedHorizontalKernelBasis, Basis.map_apply]
  rfl

theorem gradedHorizontalKernel_real_mem (K : Submodule ℚ (L ⧸ F.layer 2))
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) (hx : x ∈ K.baseChange ℝ) :
    (F.layerOneGradedMap e ω hF).baseChange ℝ x ∈ (F.gradedHorizontalKernel e ω hF K).baseChange ℝ := by
  rw [gradedHorizontalKernel, realification_map]
  exact ⟨x, hx, rfl⟩

theorem gradedHorizontalKernel_real_pure (K : Submodule ℚ (L ⧸ F.layer 2))
    (x : ℝ ⊗[ℚ] F.AssociatedGraded) (hx : x ∈ (F.gradedHorizontalKernel e ω hF K).baseChange ℝ) :
    basisGradeProjection ((bG).baseChange ℝ) ω 1 x = x := by
  rw [gradedHorizontalKernel, realification_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact F.realLayerOneGradedMap_pure e ω hF y

theorem gradedHorizontalKernelBasis_height (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ j i, RationalHeightLE ((F.layerOneBasis e ω hF).repr (b j : L ⧸ F.layer 2) i) H) :
    ∀ j i, RationalHeightLE ((bG).repr (F.gradedHorizontalKernelBasis e ω hF K b j : F.AssociatedGraded) i) H := by
  intro j i
  rw [F.gradedHorizontalKernelBasis_coe]
  exact F.layerOneGradedMap_height e ω hF _ hH (hb j) i

theorem gradedHorizontalKernelBasis_span (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K) :
    Submodule.span ℚ (Set.range (fun j =>
      (F.gradedHorizontalKernelBasis e ω hF K b j : F.AssociatedGraded))) =
        F.gradedHorizontalKernel e ω hF K := by
  change Submodule.span ℚ (Set.range ((F.gradedHorizontalKernel e ω hF K).subtype ∘
    F.gradedHorizontalKernelBasis e ω hF K b)) = _
  rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_gradedHorizontalKernel_quotient_basis [Fintype ι] [Fintype κ]
    (K : Submodule ℚ (L ⧸ F.layer 2)) (b : Basis κ ℚ K)
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ j i, RationalHeightLE ((F.layerOneBasis e ω hF).repr (b j : L ⧸ F.layer 2) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hk : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
      ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ f : Basis (Fin d) ℚ (F.AssociatedGraded ⧸ F.gradedHorizontalKernel e ω hF K),
        ∀ i j, RationalHeightLE (f.repr ((F.gradedHorizontalKernel e ω hF K).mkQ (bG j)) i) H' := by
  exact exists_submodule_quotient_basis_exp bG (F.gradedHorizontalKernel e ω hF K)
    (fun j => (F.gradedHorizontalKernelBasis e ω hF K b j : F.AssociatedGraded))
    (F.gradedHorizontalKernelBasis_span e ω hF K b) hH
    (F.gradedHorizontalKernelBasis_height e ω hF K b hH hb) hp hk hHp

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

abbrev TopGradedBasisIndex (s : ℕ) (ω : ι → ℕ) := {i : ι // s + 1 ≤ ω i}

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

noncomputable def fullFastDiagonalGenerators
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) :
    κ ⊕ TopGradedBasisIndex s ω → F.AssociatedGraded :=
  Sum.elim (fun j => F.quotientTopGradedSection e ω hF (F.reducedSquareGradedSndMap (v j)))
    (fun i => F.associatedGradedBasis e ω hF i.val)

theorem fullFastDiagonalGenerators_span
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (F.fullFastDiagonalGenerators e ω hF v)) =
      (F.fullFastGradedDiagonal W).toSubmodule := by
  have himage : Submodule.span ℚ (Set.range (fun j => F.reducedSquareGradedSndMap (v j))) =
      (F.fastGradedDiagonal W).toSubmodule := by
    change _ = W.toSubmodule.map F.reducedSquareGradedSndMap.toLinearMap
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hker : Submodule.span ℚ (Set.range (fun i : TopGradedBasisIndex s ω =>
      F.associatedGradedBasis e ω hF i.val)) = LinearMap.ker F.quotientTopGradedMap.toLinearMap := by
    rw [F.quotientTopGradedMap_kernel e ω hF]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  exact split_preimage_spanning F.quotientTopGradedMap.toLinearMap
    (F.quotientTopGradedSection e ω hF) (F.quotientTopGradedSection_rightInverse e ω hF)
    (F.fastGradedDiagonal W).toSubmodule (fun j => F.reducedSquareGradedSndMap (v j)) himage
    (fun i : TopGradedBasisIndex s ω => F.associatedGradedBasis e ω hF i.val) hker

theorem fullFastDiagonalGenerators_height
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∀ j i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
      (F.fullFastDiagonalGenerators e ω hF v j) i) H := by
  intro j i
  cases j with
  | inl j =>
    change RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
      (F.quotientTopGradedSection e ω hF (F.reducedSquareGradedSndMap (v j))) i) H
    by_cases hi : s + 1 ≤ ω i
    · rw [F.quotientTopGradedSection_coordinate_zero e ω hF _ i hi]
      exact rationalHeightLE_zero hH
    · rw [F.quotientTopGradedSection_coordinate e ω hF _ ⟨i, hi⟩,
        F.reducedSquareGradedSndMap_coordinate]
      exact hv j _
  | inr j =>
    exact (basis_repr_height_one (F.associatedGradedBasis e ω hF) j.val i).mono hH

theorem fullFastDiagonalGenerators_card [Fintype κ] [Fintype ι] :
    Fintype.card (κ ⊕ TopGradedBasisIndex s ω) ≤ Fintype.card κ + Fintype.card ι := by
  rw [Fintype.card_sum]
  exact Nat.add_le_add_left (Fintype.card_le_of_injective Subtype.val Subtype.val_injective) _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct Matrix

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

noncomputable def fullFastHorizontalGenerators
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) :
    κ ⊕ TopGradedBasisIndex s ω → L ⧸ F.layer 2 :=
  fun j => F.gradedLayerOneProjection e ω hF (F.fullFastDiagonalGenerators e ω hF v j)

theorem fullFastHorizontalGenerators_span
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (F.fullFastHorizontalGenerators e ω hF v)) =
      F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W) :=
  F.gradedLayerOneProjection_spanning e ω hF (F.fullFastGradedDiagonal W)
    (F.fullFastGradedDiagonal_graded e ω hF W hW) (F.fullFastDiagonalGenerators e ω hF v)
    (F.fullFastDiagonalGenerators_span e ω hF W v hv)

theorem fullFastHorizontalGenerators_height
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∀ j i, RationalHeightLE ((F.layerOneBasis e ω hF).repr
      (F.fullFastHorizontalGenerators e ω hF v j) i) H := by
  intro j
  exact F.gradedLayerOneProjection_height e ω hF (F.fullFastDiagonalGenerators e ω hF v j)
    (F.fullFastDiagonalGenerators_height e ω hF v hH hv j)

noncomputable def fullFastHorizontalMatrix
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) :
    Matrix (LayerOneBasisIndex ω) (κ ⊕ TopGradedBasisIndex s ω) ℚ :=
  fun i j => (F.layerOneBasis e ω hF).repr (F.fullFastHorizontalGenerators e ω hF v j) i

theorem fullFastHorizontalMatrix_height
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∀ i j, RationalHeightLE (F.fullFastHorizontalMatrix e ω hF v i j) H := by
  intro i j
  exact F.fullFastHorizontalGenerators_height e ω hF v hH hv j i

noncomputable def fullFastHorizontalCoordinates [Fintype ι]
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    Submodule ℝ (LayerOneBasisIndex ω → ℝ) :=
  ((F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ).map
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun.toLinearMap

theorem mem_fullFastHorizontalCoordinates [Fintype ι]
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x ∈
        F.fullFastHorizontalCoordinates e ω hF W ↔
      x ∈ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ := by
  rw [fullFastHorizontalCoordinates, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem fullFastHorizontalMatrix_span [Fintype ι]
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℝ (Set.range ((F.fullFastHorizontalMatrix e ω hF v).map (Rat.castHom ℝ)).col) =
      F.fullFastHorizontalCoordinates e ω hF W := by
  have hspan : Submodule.span ℝ (Set.range (fun j => (1 : ℝ) ⊗ₜ[ℚ]
      F.fullFastHorizontalGenerators e ω hF v j)) =
      (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ := by
    rw [← F.fullFastHorizontalGenerators_span e ω hF W hW v hv,
      Submodule.baseChange_span, ← Set.range_comp]
    rfl
  rw [fullFastHorizontalCoordinates, ← hspan, Submodule.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j i
  change ((F.layerOneBasis e ω hF).repr (F.fullFastHorizontalGenerators e ω hF v j) i : ℝ) =
    ((F.layerOneBasis e ω hF).baseChange ℝ).repr
      ((1 : ℝ) ⊗ₜ[ℚ] F.fullFastHorizontalGenerators e ω hF v j) i
  rw [Basis.baseChange_repr_tmul]
  simp only [Rat.smul_def, mul_one]

end Erdos3.NilpotentLieFiltration

end

end OAI
