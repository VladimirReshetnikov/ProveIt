import OAI.Combinatorics.Progressions.Estimates.EmptyLayerDetectionGeometry
import OAI.Combinatorics.Progressions.Geometry.NormalizedChartLift
import OAI.Combinatorics.Progressions.Geometry.SmallBoxCutoff

namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalAmbientKernel (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (v : D → ℝ) : ℝ :=
  smallBoxCutoff v * mixedAmbientInterpolation W b o c w f v

theorem canonicalAmbientKernel_support (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (v : D → ℝ) (hv : canonicalAmbientKernel W b o c w f v ≠ 0) :
    ∀ i, |v i| < 1/2 :=
  smallBoxCutoff_support v (left_ne_zero_of_mul hv)

theorem canonicalAmbientKernel_eq_of_lift (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    (hs : ∀ x, mixedCoefficientDensity c w p x ≠ 0 → ∀ d,
      |normalizedLatticePoint W b (orthonormalMixedChart o x) d| ≤ 1/4)
    (u : W) (v : D → ℝ)
    (hv : u.val - (EuclideanSpace.equiv D ℝ).symm v ∈ standardEuclideanLattice D)
    (hsmall : ∀ d, |v d| < 1/2) :
    canonicalAmbientKernel W b o c w f v = canonicalMixedDensity W b hb o c w p
      (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) := by
  obtain ⟨y, hy, hq⟩ := exists_normalized_chart_lift W b hb u _ hv
  let x := (orthonormalMixedChart o).symm y
  have hx : normalizedLatticePoint W b (orthonormalMixedChart o x) =
      (EuclideanSpace.equiv D ℝ).symm v := by
    simpa only [x, MeasurableEquiv.apply_symm_apply] using hy
  have hqx : normalizedLatticeQuotient W b hb (orthonormalMixedChart o x) =
      QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u := by
    simpa only [x, MeasurableEquiv.apply_symm_apply] using hq
  have hgrid : mixedAmbientInterpolation W b o c w f v =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        mixedCoefficientDensity c w p x := by
    simpa only [Prod.mk.eta, hx, ContinuousLinearEquiv.apply_symm_apply] using
      mixedAmbientInterpolation_grid W b o c w f p hf x.1 x.2
  have hd : canonicalMixedDensity W b hb o c w p
      (QuotientAddGroup.mk' (latticeSection (standardEuclideanLattice D) W).toAddSubgroup u) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        mixedCoefficientDensity c w p x := by
    rw [← hqx]
    apply canonicalMixedDensity_apply W b hb o
    rw [hx]
    exact hsmall
  rw [canonicalAmbientKernel, hgrid, hd]
  by_cases hzero : mixedCoefficientDensity c w p x = 0
  · rw [hzero, mul_zero, mul_zero]
  · have hquarter : ∀ d, |v d| ≤ 1/4 := by
      have hh := hs x hzero
      rw [hx] at hh
      exact hh
    rw [smallBoxCutoff_one v hquarter, one_mul]

theorem canonicalAmbientKernel_bounds (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    {M J C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧ mixedDensityInterpolation c w f x ≤ M)
    (hJ : LipschitzWith J (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V) :
    (∀ x, 0 ≤ canonicalAmbientKernel W b o c w f x ∧
      canonicalAmbientKernel W b o c w f x ≤ V * M) ∧
    LipschitzWith (V * (J * (C * Fintype.card D)) + (V * M) * 8)
      (canonicalAmbientKernel W b o c w f) := by
  obtain ⟨hcap, hlip⟩ := mixedAmbientInterpolation_bounds W b o c w f hM hJ hC hV
  refine ⟨?_, smallBoxCutoff_mul_lipschitz _ hlip ?_⟩
  · intro x
    refine ⟨mul_nonneg (smallBoxCutoff_range x).1 (hcap x).1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (smallBoxCutoff_range x).2 (hcap x).1).trans
      (by simpa only [one_mul] using (hcap x).2)
  · intro x
    rw [abs_of_nonneg (hcap x).1]
    exact (hcap x).2

end Erdos3

end

end OAI
