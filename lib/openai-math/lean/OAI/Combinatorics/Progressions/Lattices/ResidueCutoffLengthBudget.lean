import OAI.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def scalarCubeCutoffDerivativeNumerator (I : Type*) [Fintype I]
    (A : ℝ≥0) : ℝ :=
  (2 * 2 ^ Fintype.card I : ℕ) * ((A : ℝ) * ((Fintype.card I : ℝ) + 1))

theorem scalarCubeCutoffLipschitzConstant_eq (I : Type*) [Fintype I] (A r : ℝ≥0) :
    (scalarCubeCutoffLipschitzConstant I A r : ℝ) =
      scalarCubeCutoffDerivativeNumerator I A / r := by
  simp only [scalarCubeCutoffLipschitzConstant, scalarCubeCutoffDerivativeNumerator,
    NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one]
  ring

theorem scalarCubeResidueCutoffBudget_le_inverse_radius (I : Type*)
    [Fintype I] [DecidableEq I] (A : ℝ≥0) {r : ℝ≥0} (hr : 0 < r) (hr1 : r ≤ 1)
    (L M : ℕ) :
    scalarCubeResidueCutoffBudget I A r L M ≤ scalarCubeBoundaryConstant I * r +
      (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) +
        scalarCubeCutoffDerivativeNumerator I A) * M / (r * L) := by
  have hD : 0 ≤ 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) :=
    div_nonneg (by positivity [scalarCubeGridBoundaryConstant_pos I])
      (scalarCubeDomain_volumeReal_pos I).le
  have hr' : (0 : ℝ) < r := hr
  have hr1' : (r : ℝ) ≤ 1 := hr1
  have hscale : 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) ≤
      (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I)) / r := by
    exact (le_div_iff₀ hr').mpr (mul_le_of_le_one_right hD hr1')
  unfold scalarCubeResidueCutoffBudget
  rw [scalarCubeCutoffLipschitzConstant_eq]
  apply add_le_add le_rfl
  calc
    _ ≤ ((2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I)) / r +
        scalarCubeCutoffDerivativeNumerator I A / r) * ((M : ℝ) / L) :=
      mul_le_mul_of_nonneg_right (add_le_add hscale le_rfl) (by positivity)
    _ = _ := by ring

theorem scalarCubeResidueCutoffBudget_le_of_length (I : Type*)
    [Fintype I] [DecidableEq I] (A : ℝ≥0) {r : ℝ≥0} (hr : 0 < r) (hr1 : r ≤ 1)
    {L M : ℕ} (hL : 0 < L) {η : ℝ} (hη : 0 < η)
    (hradius : scalarCubeBoundaryConstant I * r ≤ η / 2)
    (hlength : 2 *
      (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) +
        scalarCubeCutoffDerivativeNumerator I A) * M / (r * η) ≤ L) :
    scalarCubeResidueCutoffBudget I A r L M ≤ η := by
  have hr' : (0 : ℝ) < r := hr
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have h := (div_le_iff₀ (mul_pos hr' hη)).mp hlength
  have hmesh :
      (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) +
        scalarCubeCutoffDerivativeNumerator I A) * M / (r * L) ≤ η / 2 := by
    apply (div_le_iff₀ (mul_pos hr' hL')).mpr
    nlinarith
  exact (scalarCubeResidueCutoffBudget_le_inverse_radius I A hr hr1 L M).trans
    (by linarith)

end Erdos3

end

end OAI
