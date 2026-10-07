import OAI.Combinatorics.Progressions.Estimates.EmptyLayerDetectionGeometry

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators

noncomputable def earlyConstantDensityCap (a n : ℕ) (R V : ℝ) : ℝ :=
  V * (R / 4)⁻¹ ^ a * (8 * (probabilityProfileLipschitz : ℝ) / (R / 4)) ^ n

theorem earlyConstantDensityCap_nonneg (a n : ℕ) {R V : ℝ} (hR : 0 < R) (hV : 0 ≤ V) :
    0 ≤ earlyConstantDensityCap a n R V := by
  unfold earlyConstantDensityCap
  positivity

theorem canonicalMixedDensity_constant_cap {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)
    {R V : ℝ} (hR : 0 < R) (hV : 0 ≤ V) (hv : mixedDensityCovolumeRatio W b ≤ V)
    (y : W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) :
    canonicalMixedDensity W b hb o (fun _ => 0) (fun _ => R / 4)
        (latticeConstantMass W b (fun _ => R / 4) (fun _ => div_pos hR (by norm_num))) y ≤
      earlyConstantDensityCap (Fintype.card I) n R V := by
  have hvolume : ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) ≤
      V * ∏ i, (basisAxisScale b i : ℝ) :=
    (div_le_iff₀ (Finset.prod_pos (fun i _ => basisAxisScale_cast_pos b i))).mp hv
  have hbound (x : W × (Fin n → ℤ)) :
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        orthonormalMixedDensity o (fun _ => 0) (fun _ => R / 4)
          (latticeConstantMass W b (fun _ => R / 4) (fun _ => div_pos hR (by norm_num))) x ≤
        earlyConstantDensityCap (Fintype.card I) n R V := by
    change ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
      constantCoefficientDensity (fun _ : I => R / 4) (fun i => (basisAxisScale b i : ℝ))
        (fun _ => R / 4) (basisAxisScale_cast_pos b) (fun _ => div_pos hR (by norm_num))
        ((orthonormalMixedChart o).symm x) ≤ _
    have hc := constantCoefficientDensity_cap (fun _ : I => R / 4)
      (fun _ => div_pos hR (by norm_num)) (fun i => (basisAxisScale b i : ℝ))
      (fun _ => R / 4) (basisAxisScale_cast_pos b) (fun _ => div_pos hR (by norm_num))
      hV hvolume ((orthonormalMixedChart o).symm x)
    exact hc.trans_eq (by simp only [earlyConstantDensityCap, profileWidthFactor,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  exact normalizedQuotientDensity_bound W b hb (standardLatticeSmallBox_isOpen D).measurableSet
    (Set.Subset.rfl) _ (earlyConstantDensityCap_nonneg _ _ hR hV) hbound y

end Erdos3

end

end OAI
