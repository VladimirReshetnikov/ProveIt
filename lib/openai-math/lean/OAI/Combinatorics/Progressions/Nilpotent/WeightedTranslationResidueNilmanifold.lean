import OAI.Combinatorics.Progressions.Lattices.WeightedTranslationResidueLattice

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

noncomputable def weightedTranslationResidueNilmanifold (M : ℕ) (hM : 0 < M) :
    RationalFilteredNilmanifold (weightedSubalgebra w d) d (Fintype.card (WeightedBasisIndex w d)) where
  filtration := weightedFiltration w d hwd
  basis := weightedOrderedBasis w d hw
  layerBasis i := weightedLayerFinBasis w d hw hwd (i.val+1)
  lattice := weightedTranslationResidueLattice w d hw hwd M
  grid := d.factorial * M
  grid_pos := Nat.mul_pos (Nat.factorial_pos d) hM
  inner_grid := weightedTranslationResidueLattice_inner_grid w d hw hwd M
  outer_grid := weightedTranslationResidueLattice_outer_grid w d hw hwd M

theorem weightedTranslationResidueNilmanifold_complexity_add_log
    (M : ℕ) (hM : 0 < M) {p : ℝ}
    (hG : (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
      (p + Real.log (M : ℝ)) := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt hM))
  have hp : p ≤ p + Real.log (M : ℝ) := le_add_of_nonneg_right hlog
  obtain ⟨hdim, hgrid, hstructure, hlayer⟩ := hG
  refine ⟨hdim.trans hp, ?_, fun i j k => (hstructure i j k).trans hp,
    fun i j k => (hlayer i j k).trans hp⟩
  change ((d.factorial * M : ℕ) : ℝ) ≤ Real.exp (p + Real.log (M : ℝ))
  rw [Nat.cast_mul, Real.exp_add, Real.exp_log hMr]
  exact mul_le_mul_of_nonneg_right hgrid hMr.le

theorem weightedTranslationResidueNilmanifold_complexity_budget (M : ℕ) (hM : 0 < M) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
      (((Fintype.card σ + (Fintype.card σ + 1)^d + d.factorial + 2*d + 1 : ℕ) : ℝ) +
        Real.log (M : ℝ)) :=
  weightedTranslationResidueNilmanifold_complexity_add_log w d hw hwd M hM
    (weightedTranslationNilmanifold_complexity_budget w d hw hwd)

end Erdos3.PolynomialTranslationLie

end

end OAI
