import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationStructureConstants

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ)
  (hw : ∀ i, 0 < w i) [Fintype (WeightedBasisIndex w d)]

noncomputable def weightedIndexOrder :
    WeightedBasisIndex w d ≃ Fin (Fintype.card (WeightedBasisIndex w d)) :=
  let ρ := Fintype.equivFin (WeightedBasisIndex w d)
  let u := fun j => weightedBasisGrade w d (ρ.symm j)
  ρ.trans (Tuple.sort u).symm

noncomputable def weightedOrderedBasis :
    Basis (Fin (Fintype.card (WeightedBasisIndex w d))) ℚ (weightedSubalgebra w d) :=
  (weightedBasis w d hw).reindex (weightedIndexOrder w d)

noncomputable def weightedOrderedGrade (j : Fin (Fintype.card (WeightedBasisIndex w d))) : ℕ :=
  weightedBasisGrade w d ((weightedIndexOrder w d).symm j)

omit [Fintype σ] in
theorem weightedOrderedGrade_monotone : Monotone (weightedOrderedGrade w d) :=
  Tuple.monotone_sort (fun j => weightedBasisGrade w d ((Fintype.equivFin (WeightedBasisIndex w d)).symm j))

include hw in
omit [Fintype σ] in
theorem weightedOrderedGrade_pos (j : Fin (Fintype.card (WeightedBasisIndex w d))) :
    0 < weightedOrderedGrade w d j := weightedBasisGrade_pos w d hw _

omit [Fintype σ] in
theorem weightedOrderedGrade_le (hwd : ∀ i, w i ≤ d)
    (j : Fin (Fintype.card (WeightedBasisIndex w d))) : weightedOrderedGrade w d j ≤ d :=
  weightedBasisGrade_le w d hwd _

theorem weightedOrderedBasis_layers (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    (weightedFiltration w d hwd).layer r = Submodule.span ℚ
      (weightedOrderedBasis w d hw '' {j | r ≤ weightedOrderedGrade w d j}) := by
  change (weightedFiltration w d hwd).layer r = Submodule.span ℚ
    (((weightedBasis w d hw).reindex (weightedIndexOrder w d)) ''
      {j | r ≤ weightedBasisGrade w d ((weightedIndexOrder w d).symm j)})
  rw [basis_reindex_span_weights, ← weightedFiltration_layer_eq_span w d hw hwd r]

theorem weightedOrderedBasis_central (hwd : ∀ i, w i ≤ d) :
    IsCentralLieBasis (weightedOrderedBasis w d hw) :=
  centralLieBasis_of_sorted_filtration (weightedFiltration w d hwd)
    (weightedOrderedBasis w d hw) (weightedOrderedGrade w d)
    (weightedOrderedGrade_monotone w d) (weightedOrderedBasis_layers w d hw hwd)

noncomputable def weightedLayerBasis (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    Basis {j : Fin (Fintype.card (WeightedBasisIndex w d)) // r ≤ weightedOrderedGrade w d j}
      ℚ ((weightedFiltration w d hwd).layer r) :=
  supportedSubmoduleBasis (weightedOrderedBasis w d hw) ((weightedFiltration w d hwd).layer r)
    {j | r ≤ weightedOrderedGrade w d j} (weightedOrderedBasis_layers w d hw hwd r)

theorem weightedLayerBasis_height (hwd : ∀ i, w i ≤ d) (r : ℕ)
    (i : {j : Fin (Fintype.card (WeightedBasisIndex w d)) // r ≤ weightedOrderedGrade w d j}) (j) :
    RationalHeightLE ((weightedOrderedBasis w d hw).repr
      (weightedLayerBasis w d hw hwd r i).val j) 1 := by
  rw [weightedLayerBasis, supportedSubmoduleBasis_coe]
  exact basis_repr_height_one (weightedOrderedBasis w d hw) _ _

noncomputable def weightedLayerIndexEquiv (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    {j : Fin (Fintype.card (WeightedBasisIndex w d)) // r ≤ weightedOrderedGrade w d j} ≃
      Fin (finrank ℚ ((weightedFiltration w d hwd).layer r)) := by
  classical
  exact Fintype.equivFinOfCardEq (finrank_eq_card_basis (weightedLayerBasis w d hw hwd r)).symm

noncomputable def weightedLayerFinBasis (hwd : ∀ i, w i ≤ d) (r : ℕ) :
    Basis (Fin (finrank ℚ ((weightedFiltration w d hwd).layer r)))
      ℚ ((weightedFiltration w d hwd).layer r) :=
  (weightedLayerBasis w d hw hwd r).reindex (weightedLayerIndexEquiv w d hw hwd r)

theorem weightedLayerFinBasis_height (hwd : ∀ i, w i ≤ d) (r : ℕ) (i j) :
    RationalHeightLE ((weightedOrderedBasis w d hw).repr
      (weightedLayerFinBasis w d hw hwd r i).val j) 1 := by
  rw [weightedLayerFinBasis, Basis.reindex_apply]
  exact weightedLayerBasis_height w d hw hwd r _ _

include hw in
theorem weightedBasisIndex_card_le :
    Fintype.card (WeightedBasisIndex w d) ≤ Fintype.card σ + (Fintype.card σ + 1)^d := by
  rw [← finrank_eq_card_basis (weightedBasis w d hw)]
  exact weightedSubalgebra_finrank_le w d hw

@[simp] theorem weightedOrderedBasis_repr (x : weightedSubalgebra w d)
    (i : Fin (Fintype.card (WeightedBasisIndex w d))) :
    (weightedOrderedBasis w d hw).repr x i =
      (weightedBasis w d hw).repr x ((weightedIndexOrder w d).symm i) :=
  Basis.repr_reindex_apply _ _ _ _

theorem weightedOrderedBasis_structure_height (a b c) :
    RationalHeightLE (lieStructureConstants (weightedOrderedBasis w d hw) a b c) (2 * d + 1) := by
  rw [weightedOrderedBasis, lieStructureConstants_reindex]
  exact weightedBasis_structure_height w d hw _ _ _

theorem weightedOrderedBasis_structure_height_succ (a b c) :
    RationalHeightLE (lieStructureConstants (weightedOrderedBasis w d hw) a b c) (d + 1) := by
  rw [weightedOrderedBasis, lieStructureConstants_reindex]
  exact weightedBasis_structure_height_succ w d hw _ _ _

end Erdos3.PolynomialTranslationLie

end

end OAI
