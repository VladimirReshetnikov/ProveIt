import OAI.Combinatorics.Progressions.Lattices.WeightedTranslationLattice
import OAI.Combinatorics.Progressions.Linear.WeightedTranslationOrderedBasis

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module
variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedOrderedBasis_inner_grid :
    scaledIntegerGrid d.factorial ⊆
      bchSubgroupCoordinates (weightedOrderedBasis w d hw) (weightedTranslationLattice w d hwd) :=
  bchSubgroup_inner_grid_reindex (weightedBasis w d hw) (weightedIndexOrder w d) _
    (weightedTranslationLattice_inner_grid w d hw hwd)

theorem weightedOrderedBasis_outer_grid :
    bchSubgroupCoordinates (weightedOrderedBasis w d hw) (weightedTranslationLattice w d hwd) ⊆
      denominatorGrid d.factorial :=
  bchSubgroup_outer_grid_reindex (weightedBasis w d hw) (weightedIndexOrder w d) _
    (weightedTranslationLattice_outer_grid w d hw hwd)

noncomputable def weightedTranslationNilmanifold :
    RationalFilteredNilmanifold (weightedSubalgebra w d) d (Fintype.card (WeightedBasisIndex w d)) where
  filtration := weightedFiltration w d hwd
  basis := weightedOrderedBasis w d hw
  layerBasis i := weightedLayerFinBasis w d hw hwd (i.val+1)
  lattice := weightedTranslationLattice w d hwd
  grid := d.factorial
  grid_pos := Nat.factorial_pos d
  inner_grid := weightedOrderedBasis_inner_grid w d hw hwd
  outer_grid := weightedOrderedBasis_outer_grid w d hw hwd

theorem weightedTranslationNilmanifold_complexity {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (WeightedBasisIndex w d) : ℝ) ≤ p)
    (hgrid : (d.factorial : ℝ) ≤ Real.exp p)
    (hstructure : ((2*d+1 : ℕ) : ℝ) ≤ Real.exp p) :
    (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p := by
  refine ⟨hdim,hgrid,?_,?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (weightedOrderedBasis_structure_height w d hw i j k) hstructure
  · intro i j k
    exact rationalLogHeight_le_of_height (weightedLayerFinBasis_height w d hw hwd (i.val+1) j k)
      (by simpa using Real.one_le_exp_iff.mpr hp)

theorem weightedTranslationNilmanifold_complexity_budget :
    (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE
      ((Fintype.card σ + (Fintype.card σ + 1)^d + d.factorial + 2*d + 1 : ℕ) : ℝ) := by
  let n := Fintype.card σ + (Fintype.card σ + 1)^d + d.factorial + 2*d + 1
  have hdim : (Fintype.card (WeightedBasisIndex w d) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (weightedBasisIndex_card_le w d hw).trans
      (show Fintype.card σ + (Fintype.card σ + 1)^d ≤ n by dsimp [n]; omega)
  have hf : (d.factorial : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show d.factorial ≤ n by dsimp [n]; omega)
  have hs : ((2*d+1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 2*d+1 ≤ n by dsimp [n]; omega)
  have he : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  exact weightedTranslationNilmanifold_complexity w d hw hwd (Nat.cast_nonneg n)
    hdim (hf.trans he) (hs.trans he)

end Erdos3.PolynomialTranslationLie

end

end OAI
