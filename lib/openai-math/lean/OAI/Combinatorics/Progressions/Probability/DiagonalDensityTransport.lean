import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OAI.Combinatorics.Progressions.Lattices.AffineBoxTest
import OAI.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

noncomputable def inverseJacobian (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : ℝ :=
  |LinearMap.det A.symm.toLinearEquiv.toLinearMap|

theorem inverseJacobian_pos (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : 0 < inverseJacobian A :=
  abs_pos.mpr A.symm.toLinearEquiv.isUnit_det'.ne_zero

theorem inverseJacobian_eq (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    inverseJacobian A = |LinearMap.det A.toLinearEquiv.toLinearMap|⁻¹ := by
  unfold inverseJacobian
  rw [show A.symm.toLinearEquiv = A.toLinearEquiv.symm from rfl,
    LinearEquiv.det_coe_symm, abs_inv]

variable [Fintype ι]

theorem inverse_map_volume (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Measure.map A.symm volume = ENNReal.ofReal ((inverseJacobian A)⁻¹) • volume := by
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi
    A.symm.toLinearEquiv.isUnit_det'.ne_zero
  simpa only [inverseJacobian, abs_inv, LinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_toLinearEquiv] using h

theorem integral_comp_inverse_linear (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (f : (ι → ℝ) → ℝ) :
    (∫ x, f (A.symm x)) = (inverseJacobian A)⁻¹ * ∫ x, f x := by
  have h := A.symm.toHomeomorph.measurableEmbedding.integral_map (μ := volume) f
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [inverse_map_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (inverseJacobian_pos A).le)] at h
  exact h.symm

noncomputable def linearDensityPullback (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ := inverseJacobian A * f (A.symm x)

theorem linearDensityPullback_measurable (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) : Measurable (linearDensityPullback A f) :=
  measurable_const.mul (hf.comp A.symm.continuous.measurable)

omit [Fintype ι] in
theorem linearDensityPullback_nonneg (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ι → ℝ) :
    0 ≤ linearDensityPullback A f x := mul_nonneg (inverseJacobian_pos A).le (hf _)

theorem linearDensityPullback_integrable (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    {f : (ι → ℝ) → ℝ} (hf : Integrable f) : Integrable (linearDensityPullback A f) := by
  have hm : Integrable f (Measure.map A.symm volume) := by
    rw [inverse_map_volume]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (A.symm.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hm).const_mul _

theorem linearDensityPullback_integral (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (f : (ι → ℝ) → ℝ) : (∫ x, linearDensityPullback A f x) = ∫ x, f x := by
  unfold linearDensityPullback
  rw [integral_const_mul, integral_comp_inverse_linear, ← mul_assoc,
    mul_inv_cancel₀ (inverseJacobian_pos A).ne', one_mul]

theorem linearDensityPullback_test_integral (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (f φ : (ι → ℝ) → ℝ) :
    (∫ x, linearDensityPullback A f x * φ x) = ∫ u, f u * φ (A u) := by
  have heq (x : ι → ℝ) : linearDensityPullback A f x * φ x =
      linearDensityPullback A (fun u => f u * φ (A u)) x := by
    simp only [linearDensityPullback, A.apply_symm_apply, mul_assoc]
  simp_rw [heq]
  exact linearDensityPullback_integral A _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def linearBoxDensity (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    (ι → ℝ) → ℝ := linearDensityPullback A (boxProbabilityWindow ℓ 0)

noncomputable def linearBoxDensityCap (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : ℝ≥0 :=
  ⟨inverseJacobian A * ∏ i, 1 / ℓ i,
    mul_nonneg (inverseJacobian_pos A).le
      (Finset.prod_nonneg (fun i _ => div_nonneg zero_le_one (hℓ i).le))⟩

theorem linearBoxDensity_measurable (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Measurable (linearBoxDensity ℓ A) :=
  linearDensityPullback_measurable A (boxProbabilityWindow_measurable ℓ 0)

theorem linearBoxDensity_integrable (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    Integrable (linearBoxDensity ℓ A) :=
  linearDensityPullback_integrable A (boxProbabilityWindow_integrable ℓ 0)

theorem linearBoxDensity_mass (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : (∫ x, linearBoxDensity ℓ A x) = 1 := by
  unfold linearBoxDensity
  rw [linearDensityPullback_integral, boxProbabilityWindow_mass ℓ hℓ]

theorem linearBoxDensity_mem_Icc (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (x : ι → ℝ) :
    linearBoxDensity ℓ A x ∈ Set.Icc (0 : ℝ) (linearBoxDensityCap ℓ hℓ A) :=
  ⟨linearDensityPullback_nonneg A (boxProbabilityWindow_nonneg ℓ hℓ 0) x,
    mul_le_mul_of_nonneg_left (boxProbabilityWindow_cap ℓ hℓ 0 (A.symm x))
      (inverseJacobian_pos A).le⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

theorem diagonalDensityTransport_det :
    LinearMap.det (coordinateScaleEquiv a ha).toLinearMap = ∏ i, a i := by
  classical
  have hm : LinearMap.toMatrix' (coordinateScaleEquiv a ha).toLinearMap = Matrix.diagonal a := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply]
    · simp [LinearMap.toMatrix'_apply, coordinateScaleEquiv_apply, hij]
  rw [← LinearMap.det_toMatrix', hm, Matrix.det_diagonal]

noncomputable def diagonalDensityTransport (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  linearDensityPullback (coordinateScaleEquiv a ha).toContinuousLinearEquiv f

theorem diagonalDensityTransport_eq (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    diagonalDensityTransport a ha f x = |∏ i, a i|⁻¹ * f (fun i => x i / a i) := by
  unfold diagonalDensityTransport linearDensityPullback
  rw [inverseJacobian_eq]
  change |LinearMap.det (coordinateScaleEquiv a ha).toLinearMap|⁻¹ *
    f (fun i => x i / a i) = _
  rw [diagonalDensityTransport_det]

theorem diagonalDensityTransport_test_integral (f φ : (ι → ℝ) → ℝ) :
    (∫ x, diagonalDensityTransport a ha f x * φ x) =
      ∫ x, f x * φ (fun i => a i * x i) :=
  linearDensityPullback_test_integral (coordinateScaleEquiv a ha).toContinuousLinearEquiv f φ

end Erdos3

end

end OAI
