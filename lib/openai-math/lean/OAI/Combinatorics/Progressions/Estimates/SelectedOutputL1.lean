import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Geometry.ContinuousOutputBox
import OAI.Combinatorics.Progressions.Probability.SelectedDensityNormalization

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def selectedOutputSlice {I J : Type*} [Fintype J]
    (s : J ↪ I) (f : (I → ℝ) → ℝ) (x : UnselectedColumn s → ℝ) (y : J → ℝ) : ℝ :=
  f (selectedCoefficientEquiv s ℝ (x, y))

theorem selectedOutputSlice_lipschitz {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {f : (I → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (x : UnselectedColumn s → ℝ) : LipschitzWith K (selectedOutputSlice s f x) := by
  change LipschitzWith K (selectedCoefficientProfile s f ∘ Prod.mk x)
  simpa only [mul_one] using
    (selectedCoefficientProfile_lipschitz s hf).comp (LipschitzWith.prodMk_left x)

theorem selectedOutputSlice_support_right {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {f : (I → ℝ) → ℝ} {R : ℝ} (hf : ∀ v, R < ‖v‖ → f v = 0)
    (x : UnselectedColumn s → ℝ) (y : J → ℝ) (hy : R < ‖y‖) :
    selectedOutputSlice s f x y = 0 := by
  apply hf
  rw [selectedCoefficientEquiv_norm]
  exact hy.trans_le (norm_snd_le (x, y))

theorem selectedOutputSlice_support_left {I J : Type*} [Fintype I] [Fintype J]
    (s : J ↪ I) {f : (I → ℝ) → ℝ} {R : ℝ} (hf : ∀ v, R < ‖v‖ → f v = 0)
    (x : UnselectedColumn s → ℝ) (y : J → ℝ) (hx : R < ‖x‖) :
    selectedOutputSlice s f x y = 0 := by
  apply hf
  rw [selectedCoefficientEquiv_norm]
  exact hx.trans_le (norm_fst_le (x, y))

noncomputable def retainedSelectedOutputEquiv {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) :
    (W × (UnselectedColumn s → ℝ)) × (J → ℝ) ≃ᵐ W × (I → ℝ) :=
  MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl W).prodCongr (selectedCoefficientMeasurableEquiv s))

theorem retainedSelectedOutputEquiv_preserving {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) (μ : Measure W) [SFinite μ] :
    MeasurePreserving (retainedSelectedOutputEquiv (W := W) s)
      ((μ.prod volume).prod volume) (μ.prod volume) :=
  ((MeasurePreserving.id μ).prod (selectedCoefficientMeasurableEquiv_preserving s)).comp
    (measurePreserving_prodAssoc μ volume volume)

theorem retainedSelectedOutput_integrable {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) (μ : Measure W) [SFinite μ]
    {f : W × (I → ℝ) → ℝ} (hf : Integrable f (μ.prod volume)) :
    Integrable (fun p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ) =>
      f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2))) ((μ.prod volume).prod volume) :=
  (retainedSelectedOutputEquiv_preserving s μ).integrable_comp_of_integrable hf

theorem retainedSelectedOutput_integral {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) (μ : Measure W) [SFinite μ] (f : W × (I → ℝ) → ℝ) :
    (∫ p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ),
      f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2)) ∂(μ.prod volume).prod volume) =
      ∫ p, f p ∂μ.prod volume :=
  (retainedSelectedOutputEquiv_preserving s μ).integral_comp
    (retainedSelectedOutputEquiv (W := W) s).measurableEmbedding f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selectedOutput_restricted_l1 {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (s : J ↪ I) (μ : Measure W) [SFinite μ]
    (R : ℝ≥0) (f : W × (I → ℝ) → ℝ) (hf : Integrable f (μ.prod volume))
    {ε : ℝ} (he : (∫ p, |f p| ∂μ.prod volume) ≤ ε) :
    let ν := μ.prod (continuousOutputBoxMeasure (UnselectedColumn s) R)
    let F := fun p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ) =>
      f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2))
    Integrable F (ν.prod volume) ∧ (∫ p, |F p| ∂ν.prod volume) ≤ ε := by
  dsimp only
  have hi := retainedSelectedOutput_integrable s μ hf
  have hle : (μ.prod (continuousOutputBoxMeasure (UnselectedColumn s) R)).prod volume ≤
      (μ.prod (volume : Measure (UnselectedColumn s → ℝ))).prod (volume : Measure (J → ℝ)) :=
    Measure.prod_mono (Measure.prod_mono le_rfl (continuousOutputBoxMeasure_le _ R)) le_rfl
  refine ⟨hi.mono_measure hle, ?_⟩
  have ha : Integrable (fun p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ) =>
      |f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2))|) ((μ.prod volume).prod volume) := by
    simpa only [Real.norm_eq_abs] using hi.norm
  calc
    _ ≤ ∫ p : (W × (UnselectedColumn s → ℝ)) × (J → ℝ),
        |f (p.1.1, selectedCoefficientEquiv s ℝ (p.1.2, p.2))| ∂(μ.prod volume).prod volume :=
      integral_mono_measure hle (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) ha
    _ = ∫ p, |f p| ∂μ.prod volume := retainedSelectedOutput_integral s μ (fun p => |f p|)
    _ ≤ ε := he

end Erdos3

end

end OAI
