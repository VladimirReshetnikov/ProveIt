import OAI.Combinatorics.Progressions.Probability.DiagonalDensityTransport

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem map_volume_positive_diagonal (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Measure.map (fun v : ι → ℝ => fun i => a i * v i) volume =
      ENNReal.ofReal (∏ i, a i)⁻¹ • volume := by
  classical
  have hp : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => ha i)
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (coordinateScaleEquiv a (fun i => (ha i).ne')).isUnit_det'.ne_zero
  rw [diagonalDensityTransport_det] at h
  change Measure.map (fun v : ι → ℝ => fun i => a i * v i) volume =
    ENNReal.ofReal |(∏ i, a i)⁻¹| • volume at h
  simpa only [abs_of_pos (inv_pos.mpr hp)] using h

theorem map_volume_positive_diagonal_normalize (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    Measure.map (fun v : ι → ℝ => fun i => v i / a i) volume =
      ENNReal.ofReal (∏ i, a i) • volume := by
  classical
  have h := map_volume_positive_diagonal (fun i => (a i)⁻¹)
    (fun i => inv_pos.mpr (ha i))
  simpa only [Finset.prod_inv_distrib, inv_inv, div_eq_mul_inv, mul_comm] using h

theorem complex_integral_comp_positive_diagonal (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (f : (ι → ℝ) → ℂ) :
    (∫ v : ι → ℝ, f (fun i => a i * v i)) =
      ((∏ i, a i : ℝ) : ℂ)⁻¹ * ∫ v : ι → ℝ, f v := by
  classical
  let A := (coordinateScaleEquiv a (fun i => (ha i).ne')).toContinuousLinearEquiv
  have h := A.toHomeomorph.measurableEmbedding.integral_map (μ := volume) f
  change (∫ v : ι → ℝ, f v ∂Measure.map (fun v : ι → ℝ => fun i => a i * v i) volume) =
    ∫ v : ι → ℝ, f (fun i => a i * v i) at h
  rw [map_volume_positive_diagonal a ha, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (Finset.prod_nonneg (fun i _ => (ha i).le)))] at h
  simpa only [Complex.real_smul, Complex.ofReal_inv] using h.symm

theorem complex_integral_eq_positive_diagonal (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (f : (ι → ℝ) → ℂ) :
    (∫ v : ι → ℝ, f v) = ((∏ i, a i : ℝ) : ℂ) * ∫ v : ι → ℝ, f (fun i => a i * v i) := by
  classical
  have hp : ((∏ i, a i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos (fun i _ => ha i)).ne'
  rw [complex_integral_comp_positive_diagonal a ha, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]

theorem complex_integral_comp_positive_diagonal_normalize
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (f : (ι → ℝ) → ℂ) :
    (∫ v : ι → ℝ, f (fun i => v i / a i)) = ((∏ i, a i : ℝ) : ℂ) * ∫ v : ι → ℝ, f v := by
  classical
  have h := complex_integral_comp_positive_diagonal (fun i => (a i)⁻¹)
    (fun i => inv_pos.mpr (ha i)) f
  simpa only [Finset.prod_inv_distrib, Complex.ofReal_inv, inv_inv,
    div_eq_mul_inv, mul_comm] using h

end Erdos3

end

end OAI
