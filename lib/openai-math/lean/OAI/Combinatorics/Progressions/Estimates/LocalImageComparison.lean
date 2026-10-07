import OAI.Combinatorics.Progressions.Estimates.BooleanSelectedDerivativeBound

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

theorem local_selected_inverse_image_comparison
    (ρ χ : (κ → ℝ) → ℝ) (hρ : Measurable ρ) (hρi : Integrable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρmass : (∫ x, ρ x) = 1)
    (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 (fun x => ρ x * χ x)) (hws : HasCompactSupport (fun x => ρ x * χ x))
    (F : Fin 2 → (κ → ℝ) → (ι → ℝ)) (hmF : ∀ t, Measurable (F t))
    (hF : ∀ t x, x ∈ tsupport (fun x => ρ x * χ x) → ContDiffAt ℝ 2 (F t) x)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hinv : ∀ t x, x ∈ tsupport (fun x => ρ x * χ x) → (selectedDerivative (F t) J x).IsInvertible)
    (B : ℝ≥0) (hdiv : ∀ t i, (∫ x, |coordinateDivergence
      (fun j x => (ρ x * χ x) * selectedInverseField (F t) J i j x) x|) ≤ B)
    {ε η : ℝ} (hε : 0 ≤ ε) (hcut : (∫ x, ρ x * (1 - χ x)) ≤ η)
    (hclose : ∀ x, ρ x * χ x ≠ 0 → dist (F 0 x) (F 1 x) ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, ρ x * φ (F 0 x)) - ∫ x, ρ x * φ (F 1 x)| ≤
      2 * η + 2 * (Fintype.card ι : ℝ) * B * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
  let μ := realDensityMeasure volume ρ
  let : IsProbabilityMeasure μ := realDensityMeasure_probability volume ρ hρi hρ0 hρmass
  have hT (t : Fin 2) : ImageTranslationBound (realDensityMeasure μ χ) (F t)
      ((Fintype.card ι : ℝ≥0) * B) := by
    rw [realDensityMeasure_mul volume ρ χ hρ hχ hρ0]
    have h := imageTranslationBound_of_local_selected_inverse (F t) (hmF t) J
      (fun x => ρ x * χ x) hw hws (fun x => mul_nonneg (hρ0 x) (hχ01 x).1)
      (hF t) (hinv t) (fun _ => B) (hdiv t)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hcut' : (∫ x, 1 - χ x ∂μ) ≤ η := by
    rw [realDensityMeasure_integral volume ρ hρ hρ0]
    exact hcut
  have hclose' : ∀ᵐ x ∂realDensityMeasure μ χ, dist (F 0 x) (F 1 x) ≤ ε := by
    rw [realDensityMeasure_mul volume ρ χ hρ hχ hρ0]
    exact ae_realDensityMeasure_of_forall_nonzero volume _ (hρ.mul hχ) _ hclose
  have h := cutoff_box_image_comparison μ χ hχ hχ01 (F 0) (F 1) (hmF 0) (hmF 1)
    _ _ (hT 0) (hT 1) hε hcut' hclose' δ hδ φ hφ hbound
  unfold mappedTest at h
  rw [realDensityMeasure_integral volume ρ hρ hρ0, realDensityMeasure_integral volume ρ hρ hρ0] at h
  apply h.trans_eq
  push_cast
  ring

theorem local_selected_inverse_image_comparison_sqrt
    (ρ χ : (κ → ℝ) → ℝ) (hρ : Measurable ρ) (hρi : Integrable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρmass : (∫ x, ρ x) = 1)
    (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 (fun x => ρ x * χ x)) (hws : HasCompactSupport (fun x => ρ x * χ x))
    (F : Fin 2 → (κ → ℝ) → (ι → ℝ)) (hmF : ∀ t, Measurable (F t))
    (hF : ∀ t x, x ∈ tsupport (fun x => ρ x * χ x) → ContDiffAt ℝ 2 (F t) x)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hinv : ∀ t x, x ∈ tsupport (fun x => ρ x * χ x) → (selectedDerivative (F t) J x).IsInvertible)
    (B : ℝ≥0) (hB : 0 < (B : ℝ)) (hdiv : ∀ t i, (∫ x, |coordinateDivergence
      (fun j x => (ρ x * χ x) * selectedInverseField (F t) J i j x) x|) ≤ B)
    {ε η : ℝ} (hε : 0 < ε) (hcut : (∫ x, ρ x * (1 - χ x)) ≤ η)
    (hclose : ∀ x, ρ x * χ x ≠ 0 → dist (F 0 x) (F 1 x) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, ρ x * φ (F 0 x)) - ∫ x, ρ x * φ (F 1 x)| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by
  have h := local_selected_inverse_image_comparison ρ χ hρ hρi hρ0 hρmass hχ hχ01 hw hws F hmF hF J
    hinv B hdiv hε.le hcut hclose (Real.sqrt (ε / (B : ℝ)))
    (Real.sqrt_pos.mpr (div_pos hε hB)) φ hφ hbound
  apply h.trans_eq
  have hbal := sqrt_smoothing_balance hB hε
  calc
    2 * η + 2 * (Fintype.card ι : ℝ) * B * Real.sqrt (ε / (B : ℝ)) +
        2 * (Fintype.card ι : ℝ) * ε / Real.sqrt (ε / (B : ℝ)) =
      2 * η + 2 * (Fintype.card ι : ℝ) *
        ((B : ℝ) * Real.sqrt (ε / (B : ℝ)) + ε / Real.sqrt (ε / (B : ℝ))) := by ring
    _ = 2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by rw [hbal]; ring

end Erdos3

end

end OAI
