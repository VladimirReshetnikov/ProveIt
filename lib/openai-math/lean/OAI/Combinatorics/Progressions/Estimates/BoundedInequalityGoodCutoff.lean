import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import OAI.Combinatorics.Progressions.Estimates.LocalImageComparison
import OAI.Combinatorics.Progressions.Estimates.ScalarCubeDomain
import OAI.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff

theorem sublevelCutoff_integral_loss_le {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (ψ : ℝ → ℝ) (hψ : Measurable ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ t, 2 ≤ |t| → ψ t = 1) {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) (hd : Measurable d) :
    (∫ x, 1 - sublevelCutoff ψ r d x ∂μ) ≤ μ.real {x | |d x| < 2 * r} := by
  let s := {x | |d x| < 2 * r}
  have hs : MeasurableSet s := measurableSet_lt hd.abs measurable_const
  have hf : Measurable (sublevelCutoff ψ r d) := hψ.comp (hd.div_const r)
  have hfi := cutoff_integrable μ _ hf (sublevelCutoff_range ψ hrange r d)
  calc
    _ ≤ ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      apply integral_mono ((integrable_const (1 : ℝ)).sub hfi)
        ((integrable_const (1 : ℝ)).indicator hs)
      intro x
      change 1 - sublevelCutoff ψ r d x ≤ s.indicator (fun _ => (1 : ℝ)) x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx]
        change 1 - ψ (d x / r) ≤ 1
        linarith [(hrange (d x / r)).1]
      · rw [Set.indicator_of_notMem hx]
        have hx' : 2 * r ≤ |d x| := le_of_not_gt hx
        rw [sublevelCutoff_eq_one ψ hone hr d hx']
        norm_num
    _ = _ := integral_indicator_one hs

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def goodDomainCutoff {ι E : Type*} [Fintype ι]
    (ψ : ℝ → ℝ) (r : ι → ℝ) (d : ι → E → ℝ) (b : E → ℝ) (x : E) : ℝ :=
  b x * ∏ i, sublevelCutoff ψ (r i) (d i) x

theorem goodDomainCutoff_range {ι E : Type*} [Fintype ι]
    (ψ : ℝ → ℝ) (hψ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (r : ι → ℝ) (d : ι → E → ℝ) (b : E → ℝ)
    (hb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) (x : E) :
    goodDomainCutoff ψ r d b x ∈ Set.Icc (0 : ℝ) 1 := by
  have hp := product_cutoff_range (fun i => sublevelCutoff ψ (r i) (d i) x)
    (fun i => sublevelCutoff_range ψ hψ (r i) (d i) x)
  exact ⟨mul_nonneg (hb x).1 hp.1, (mul_le_mul (hb x).2 hp.2 hp.1 zero_le_one).trans_eq (by ring)⟩

theorem goodDomainCutoff_smooth {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (r : ι → ℝ)
    (d : ι → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i))
    (b : E → ℝ) (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (goodDomainCutoff ψ r d b) :=
  hb.mul (contDiff_prod (fun i _ => contDiff_sublevelCutoff ψ hψ (r i) (d i) (hd i)))

theorem goodDomainCutoff_compact {ι E : Type*} [Fintype ι] [TopologicalSpace E]
    (ψ : ℝ → ℝ) (r : ι → ℝ) (d : ι → E → ℝ) (b : E → ℝ)
    (hb : HasCompactSupport b) : HasCompactSupport (goodDomainCutoff ψ r d b) :=
  hb.mul_right

theorem goodDomainCutoff_tsupport_subset {ι E : Type*} [Fintype ι] [TopologicalSpace E]
    (ψ : ℝ → ℝ) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (d : ι → E → ℝ) (hd : ∀ i, Continuous (d i))
    (b : E → ℝ) :
    tsupport (goodDomainCutoff ψ r d b) ⊆ tsupport b ∩ {x | ∀ i, r i ≤ |d i x|} := by
  intro x hx
  refine ⟨tsupport_mul_subset_left hx, ?_⟩
  intro i
  exact sublevelCutoff_tsupport_subset ψ hzero (hr i) (d i) (hd i)
    (product_cutoff_tsupport_subset (fun j => sublevelCutoff ψ (r j) (d j)) i
      (tsupport_mul_subset_right hx))

theorem goodDomainCutoff_eq_one {ι E : Type*} [Fintype ι]
    (ψ : ℝ → ℝ) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (d : ι → E → ℝ) (b : E → ℝ)
    {x : E} (hb : b x = 1) (hd : ∀ i, 2 * r i ≤ |d i x|) :
    goodDomainCutoff ψ r d b x = 1 := by
  unfold goodDomainCutoff
  rw [hb, one_mul]
  exact Finset.prod_eq_one (fun i _ => sublevelCutoff_eq_one ψ hone (hr i) (d i) (hd i))

theorem goodDomainCutoff_fderiv_norm_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (A : ℝ≥0) (hLip : LipschitzWith A ψ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (d : ι → E → ℝ) (b : E → ℝ) (hbrange : ∀ y, b y ∈ Set.Icc (0 : ℝ) 1)
    {x : E} (hd : ∀ i, DifferentiableAt ℝ (d i) x) (hb : DifferentiableAt ℝ b x) :
    ‖fderiv ℝ (goodDomainCutoff ψ r d b) x‖ ≤
      ‖fderiv ℝ b x‖ + ∑ i, ((A : ℝ) / r i) * ‖fderiv ℝ (d i) x‖ := by
  let f : Option ι → E → ℝ := fun o => match o with
    | none => b
    | some i => sublevelCutoff ψ (r i) (d i)
  have hfd : ∀ o, DifferentiableAt ℝ (f o) x := by
    intro o
    cases o with
    | none => exact hb
    | some i =>
      have hdi : DifferentiableAt ℝ (fun y => d i y / r i) x := by
        simpa only [div_eq_mul_inv] using (hd i).mul_const (r i)⁻¹
      exact (hψ.differentiable (by norm_num)).differentiableAt.comp x hdi
  have hfr : ∀ o, f o x ∈ Set.Icc (0 : ℝ) 1 := by
    intro o
    cases o with
    | none => exact hbrange x
    | some i => exact sublevelCutoff_range ψ hrange (r i) (d i) x
  have h := product_cutoff_fderiv_norm_le f x hfd hfr
  have heq : (fun y => ∏ o, f o y) = goodDomainCutoff ψ r d b := by
    funext y
    simp only [Fintype.prod_option, f, goodDomainCutoff]
  rw [heq] at h
  simp only [Fintype.sum_option, f] at h
  apply h.trans
  apply add_le_add le_rfl
  exact Finset.sum_le_sum (fun i _ => sublevelCutoff_fderiv_norm_le ψ hψ A hLip (hr i) (d i) (hd i))

theorem goodDomainCutoff_integral_loss_le {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ]
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hone : ∀ t, 2 ≤ |t| → ψ t = 1) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (d : ι → E → ℝ) (hd : ∀ i, Measurable (d i))
    (b : E → ℝ) (hb : Measurable b) (hbrange : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, 1 - goodDomainCutoff ψ r d b x ∂μ) ≤
      (∫ x, 1 - b x ∂μ) + ∑ i, μ.real {x | |d i x| < 2 * r i} := by
  let f : Option ι → E → ℝ := fun o => match o with
    | none => b
    | some i => sublevelCutoff ψ (r i) (d i)
  have hfm : ∀ o, Measurable (f o) := by
    intro o
    cases o with
    | none => exact hb
    | some i => exact hψ.comp ((hd i).div_const (r i))
  have hfr : ∀ o y, f o y ∈ Set.Icc (0 : ℝ) 1 := by
    intro o y
    cases o with
    | none => exact hbrange y
    | some i => exact sublevelCutoff_range ψ hrange (r i) (d i) y
  have h := product_cutoff_integral_loss_le μ f hfm hfr
  simp only [Fintype.prod_option, Fintype.sum_option, f] at h
  change (∫ x, 1 - goodDomainCutoff ψ r d b x ∂μ) ≤ _ at h
  apply h.trans
  apply add_le_add le_rfl
  exact Finset.sum_le_sum (fun i _ => sublevelCutoff_integral_loss_le μ ψ hψ hrange hone
    (hr i) (d i) (hd i))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def sublevelCutoffProduct {J E : Type*} [Fintype J]
    (ψ : ℝ → ℝ) (κ : J → ℝ) (d : J → E → ℝ) (x : E) : ℝ :=
  ∏ i, sublevelCutoff ψ (κ i) (d i) x

theorem sublevelCutoffProduct_range {J E : Type*} [Fintype J]
    (ψ : ℝ → ℝ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (κ : J → ℝ) (d : J → E → ℝ) (x : E) :
    sublevelCutoffProduct ψ κ d x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun i => sublevelCutoff_range ψ hrange (κ i) (d i) x)

theorem sublevelCutoffProduct_smooth {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (κ : J → ℝ)
    (d : J → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    ContDiff ℝ ∞ (sublevelCutoffProduct ψ κ d) :=
  contDiff_prod (fun i _ => contDiff_sublevelCutoff ψ hψ (κ i) (d i) (hd i))

theorem sublevelCutoffProduct_fderiv_norm_le {J E : Type*} [Fintype J]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (A : ℝ≥0) (hLip : LipschitzWith A ψ) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (x : E) :
    ‖fderiv ℝ (sublevelCutoffProduct ψ κ d) x‖ ≤
      ∑ i, ((A : ℝ) / κ i) * ‖fderiv ℝ (d i) x‖ := by
  have h := product_cutoff_fderiv_norm_le (fun i => sublevelCutoff ψ (κ i) (d i)) x
    (fun i => ((contDiff_sublevelCutoff ψ hψ (κ i) (d i) (hd i)).differentiable
      (by norm_num)).differentiableAt)
    (fun i => sublevelCutoff_range ψ hrange (κ i) (d i) x)
  exact h.trans (Finset.sum_le_sum (fun i _ => sublevelCutoff_fderiv_norm_le ψ hψ A hLip
    (hκ i) (d i) ((hd i).differentiable (by norm_num)).differentiableAt))

theorem sublevelCutoffProduct_integral_loss_le {J E : Type*} [Fintype J] [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (ψ : ℝ → ℝ) (hψ : Measurable ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (κ : J → ℝ) (hκ : ∀ i, 0 < κ i) (d : J → E → ℝ) (hd : ∀ i, Measurable (d i)) :
    (∫ x, 1 - sublevelCutoffProduct ψ κ d x ∂μ) ≤
      ∑ i, μ.real {x | |d i x| < 2 * κ i} := by
  have h := product_cutoff_integral_loss_le μ (fun i => sublevelCutoff ψ (κ i) (d i))
    (fun i => hψ.comp ((hd i).div_const (κ i)))
    (fun i => sublevelCutoff_range ψ hrange (κ i) (d i))
  exact h.trans (Finset.sum_le_sum (fun i _ => sublevelCutoff_integral_loss_le μ ψ hψ
    hrange hone (hκ i) (d i) (hd i)))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Topology

theorem indicator_eventuallyEq_on_open {X Y : Type*} [TopologicalSpace X] [Zero Y]
    {s : Set X} (hs : IsOpen s) (f : X → Y) {x : X} (hx : x ∈ s) :
    s.indicator f =ᶠ[𝓝 x] f := by
  filter_upwards [hs.mem_nhds hx] with y hy
  exact Set.indicator_of_mem hy f

theorem indicator_measurable_of_continuousOn {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [Zero Y] {s : Set X} (hs : MeasurableSet s)
    (f : X → Y) (hf : ContinuousOn f s) : Measurable (s.indicator f) := by
  classical
  exact hf.measurable_piecewise continuousOn_const hs

theorem integral_indicator_weight_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {s : Set X} (hs : MeasurableSet s) (f g : X → ℝ) :
    (∫ x, s.indicator f x * g x ∂μ) = ∫ x in s, f x * g x ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ s <;> simp [hx]

theorem integral_indicator_weight_image {X Y : Type*} [MeasurableSpace X] [Zero Y]
    (μ : Measure X) {s : Set X} (hs : MeasurableSet s) (ρ : X → ℝ) (F : X → Y) (φ : Y → ℝ) :
    (∫ x, s.indicator ρ x * φ (s.indicator F x) ∂μ) = ∫ x in s, ρ x * φ (F x) ∂μ := by
  rw [integral_indicator_weight_mul μ hs]
  apply setIntegral_congr_fun hs
  intro x hx
  change ρ x * φ (s.indicator F x) = ρ x * φ (F x)
  rw [Set.indicator_of_mem hx]

theorem weighted_selectedInverse_indicator_eq
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {s : Set (κ → ℝ)} (hs : IsOpen s) (w : (κ → ℝ) → ℝ) (hws : tsupport w ⊆ s)
    (U : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (i : ι) (j : κ) :
    (fun x => w x * selectedInverseField (s.indicator U) J i j x) =
      (fun x => w x * selectedInverseField U J i j x) := by
  funext x
  by_cases hx : w x = 0
  · simp only [hx, zero_mul]
  · have hEq := indicator_eventuallyEq_on_open hs U (hws (subset_tsupport w hx))
    simp only [selectedInverseField, selectedDerivative, hEq.fderiv_eq]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem exists_good_domain_cutoff :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ {ι E : Type*} [Fintype ι]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
      (μ : Measure E) [IsFiniteMeasure μ]
      (Ω : Set E) (b : E → ℝ), ContDiff ℝ ∞ b → HasCompactSupport b →
      (∀ x, b x ∈ Set.Icc (0 : ℝ) 1) → tsupport b ⊆ Ω →
      ∀ (r : ι → ℝ), (∀ i, 0 < r i) →
      ∀ (d : ι → E → ℝ), (∀ i, ContDiff ℝ ∞ (d i)) →
      ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
        tsupport χ ⊆ Ω ∩ {x | ∀ i, r i ≤ |d i x|} ∧
        (∀ x, b x = 1 → (∀ i, 2 * r i ≤ |d i x|) → χ x = 1) ∧
        (∀ x, ‖fderiv ℝ χ x‖ ≤ ‖fderiv ℝ b x‖ +
          ∑ i, ((A : ℝ) / r i) * ‖fderiv ℝ (d i) x‖) ∧
        (∫ x, 1 - χ x ∂μ) ≤ (∫ x, 1 - b x ∂μ) +
          ∑ i, μ.real {x | |d i x| < 2 * r i} := by
  obtain ⟨A, hA, ψ, hs, hrange, hzero, hone, hLip⟩ := exists_smooth_sublevel_cutoff
  refine ⟨A, hA, ?_⟩
  intro ι E _ _ _ _ _ μ _ Ω b hb hbc hbr hbs r hr d hd
  refine ⟨goodDomainCutoff ψ r d b, goodDomainCutoff_smooth ψ hs r d hd b hb,
    goodDomainCutoff_compact ψ r d b hbc, goodDomainCutoff_range ψ hrange r d b hbr,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := goodDomainCutoff_tsupport_subset ψ hzero r hr d (fun i => (hd i).continuous) b hx
    exact ⟨hbs h.1, h.2⟩
  · intro x hbx hdx
    exact goodDomainCutoff_eq_one ψ hone r hr d b hbx hdx
  · intro x
    exact goodDomainCutoff_fderiv_norm_le ψ hs hrange A hLip r hr d b hbr
      (fun i => ((hd i).differentiable (by norm_num)).differentiableAt)
      ((hb.differentiable (by norm_num)).differentiableAt)
  · exact goodDomainCutoff_integral_loss_le μ ψ hs.continuous.measurable hrange hone r hr d
      (fun i => (hd i).continuous.measurable) b hb.continuous.measurable hbr

theorem supported_density_cutoff_weight {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) (ρ χ : E → ℝ)
    (hρ : ContDiffOn ℝ 1 ρ Ω) (hχ : ContDiff ℝ 1 χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω) :
    ContDiff ℝ 1 (fun x => Ω.indicator ρ x * χ x) ∧
      HasCompactSupport (fun x => Ω.indicator ρ x * χ x) ∧
      tsupport (fun x => Ω.indicator ρ x * χ x) ⊆ Ω := by
  have hl : ∀ x ∈ tsupport χ, ContDiffAt ℝ 1 (Ω.indicator ρ) x := by
    intro x hx
    exact (hρ.contDiffAt (hΩ.mem_nhds (hs hx))).congr_of_eventuallyEq
      (indicator_eventuallyEq_on_open hΩ ρ (hs hx))
  refine ⟨?_, hc.mul_left, tsupport_mul_subset_right.trans hs⟩
  have h := contDiff_mul_of_local_right hχ hl
  simpa only [mul_comm] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

theorem open_domain_image_comparison
    (Ω : Set (κ → ℝ)) (hΩ : IsOpen Ω) (ρ χ : (κ → ℝ) → ℝ)
    (hρ : Measurable ρ) (hρi : IntegrableOn ρ Ω) (hρ0 : ∀ x ∈ Ω, 0 ≤ ρ x)
    (hρmass : (∫ x in Ω, ρ x) = 1) (hχ : Measurable χ)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 (fun x => Ω.indicator ρ x * χ x))
    (hws : HasCompactSupport (fun x => Ω.indicator ρ x * χ x))
    (hwsΩ : tsupport (fun x => Ω.indicator ρ x * χ x) ⊆ Ω)
    (F : Fin 2 → (κ → ℝ) → (ι → ℝ)) (hF : ∀ t, ContDiffOn ℝ 2 (F t) Ω)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hinv : ∀ t x, x ∈ tsupport (fun x => Ω.indicator ρ x * χ x) →
      (selectedDerivative (F t) J x).IsInvertible)
    (B : ℝ≥0) (hdiv : ∀ t i, (∫ x in Ω, |coordinateDivergence
      (fun j x => (Ω.indicator ρ x * χ x) * selectedInverseField (F t) J i j x) x|) ≤ B)
    {ε η : ℝ} (hε : 0 ≤ ε) (hcut : (∫ x in Ω, ρ x * (1 - χ x)) ≤ η)
    (hclose : ∀ x, Ω.indicator ρ x * χ x ≠ 0 → dist (F 0 x) (F 1 x) ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x in Ω, ρ x * φ (F 0 x)) - ∫ x in Ω, ρ x * φ (F 1 x)| ≤
      2 * η + 2 * (Fintype.card ι : ℝ) * B * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
  let r := Ω.indicator ρ
  let w := fun x => r x * χ x
  let G := fun t : Fin 2 => Ω.indicator (F t)
  have hr : Measurable r := hρ.indicator hΩ.measurableSet
  have hri : Integrable r := (integrable_indicator_iff hΩ.measurableSet).mpr hρi
  have hr0 (x : κ → ℝ) : 0 ≤ r x := by
    by_cases hx : x ∈ Ω
    · change 0 ≤ Ω.indicator ρ x
      rw [Set.indicator_of_mem hx]
      exact hρ0 x hx
    · simp only [r, Set.indicator_of_notMem hx, le_refl]
  have hrmass : (∫ x, r x) = 1 := by rw [integral_indicator hΩ.measurableSet, hρmass]
  have hGm (t : Fin 2) : Measurable (G t) :=
    indicator_measurable_of_continuousOn hΩ.measurableSet (F t) (hF t).continuousOn
  have hGl (t : Fin 2) (x : κ → ℝ) (hx : x ∈ tsupport w) : ContDiffAt ℝ 2 (G t) x :=
    ((hF t).contDiffAt (hΩ.mem_nhds (hwsΩ hx))).congr_of_eventuallyEq
      (indicator_eventuallyEq_on_open hΩ (F t) (hwsΩ hx))
  have hGi (t : Fin 2) (x : κ → ℝ) (hx : x ∈ tsupport w) :
      (selectedDerivative (G t) J x).IsInvertible := by
    have heq := indicator_eventuallyEq_on_open hΩ (F t) (hwsΩ hx)
    simpa only [G, selectedDerivative, heq.fderiv_eq] using hinv t x hx
  have hGdiv (t : Fin 2) (i : ι) :
      (∫ x, |coordinateDivergence (fun j x => w x * selectedInverseField (G t) J i j x) x|) ≤ B := by
    have heq : (fun j x => w x * selectedInverseField (G t) J i j x) =
        (fun j x => w x * selectedInverseField (F t) J i j x) := by
      funext j
      exact weighted_selectedInverse_indicator_eq hΩ w hwsΩ (F t) J i j
    rw [heq, integral_abs_divergence_eq_setIntegral
      (fun j x => w x * selectedInverseField (F t) J i j x) w
      (fun j => tsupport_smul_subset_left w (selectedInverseField (F t) J i j)) hwsΩ]
    exact hdiv t i
  have hcut' : (∫ x, r x * (1 - χ x)) ≤ η := by
    rw [integral_indicator_weight_mul volume hΩ.measurableSet]
    exact hcut
  have hclose' (x : κ → ℝ) (hx : w x ≠ 0) : dist (G 0 x) (G 1 x) ≤ ε := by
    have hxΩ := hwsΩ (subset_tsupport w hx)
    simpa only [G, Set.indicator_of_mem hxΩ] using hclose x hx
  have h := local_selected_inverse_image_comparison r χ hr hri hr0 hrmass hχ hχ01 hw hws
    G hGm hGl J hGi B hGdiv hε hcut' hclose' δ hδ φ hφ hbound
  change |(∫ x, Ω.indicator ρ x * φ (Ω.indicator (F 0) x)) -
    ∫ x, Ω.indicator ρ x * φ (Ω.indicator (F 1) x)| ≤ _ at h
  rw [integral_indicator_weight_image volume hΩ.measurableSet,
    integral_indicator_weight_image volume hΩ.measurableSet] at h
  exact h

theorem open_domain_image_comparison_sqrt
    (Ω : Set (κ → ℝ)) (hΩ : IsOpen Ω) (ρ χ : (κ → ℝ) → ℝ)
    (hρ : Measurable ρ) (hρi : IntegrableOn ρ Ω) (hρ0 : ∀ x ∈ Ω, 0 ≤ ρ x)
    (hρmass : (∫ x in Ω, ρ x) = 1) (hχ : Measurable χ)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 (fun x => Ω.indicator ρ x * χ x))
    (hws : HasCompactSupport (fun x => Ω.indicator ρ x * χ x))
    (hwsΩ : tsupport (fun x => Ω.indicator ρ x * χ x) ⊆ Ω)
    (F : Fin 2 → (κ → ℝ) → (ι → ℝ)) (hF : ∀ t, ContDiffOn ℝ 2 (F t) Ω)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hinv : ∀ t x, x ∈ tsupport (fun x => Ω.indicator ρ x * χ x) →
      (selectedDerivative (F t) J x).IsInvertible)
    (B : ℝ≥0) (hB : 0 < (B : ℝ)) (hdiv : ∀ t i, (∫ x in Ω, |coordinateDivergence
      (fun j x => (Ω.indicator ρ x * χ x) * selectedInverseField (F t) J i j x) x|) ≤ B)
    {ε η : ℝ} (hε : 0 < ε) (hcut : (∫ x in Ω, ρ x * (1 - χ x)) ≤ η)
    (hclose : ∀ x, Ω.indicator ρ x * χ x ≠ 0 → dist (F 0 x) (F 1 x) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x in Ω, ρ x * φ (F 0 x)) - ∫ x in Ω, ρ x * φ (F 1 x)| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by
  have h := open_domain_image_comparison Ω hΩ ρ χ hρ hρi hρ0 hρmass hχ hχ01 hw hws hwsΩ F hF J
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

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem exists_bounded_inequality_good_cutoff :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∃ B : ℝ≥0, 1 ≤ B ∧
      ∀ {I J E : Type*} [Fintype I] [Fintype J]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
      [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasure μ]
      (d : I → E → ℝ), (∀ i, ContDiff ℝ ∞ (d i)) →
      Bornology.IsBounded (positiveInequalityDomain d) →
      ∀ (r : I → ℝ), (∀ i, 0 < r i) →
      ∀ (p : J → E → ℝ), (∀ j, ContDiff ℝ ∞ (p j)) →
      ∀ (κ : J → ℝ), (∀ j, 0 < κ j) →
      ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
        tsupport χ ⊆ positiveInequalityDomain d ∩ {x | ∀ j, κ j ≤ |p j x|} ∧
        (∀ x, (∀ i, 2 * r i ≤ d i x) → (∀ j, 2 * κ j ≤ |p j x|) → χ x = 1) ∧
        (∀ x, ‖fderiv ℝ χ x‖ ≤
          (∑ i, ((A : ℝ) / r i) * ‖fderiv ℝ (d i) x‖) +
          ∑ j, ((B : ℝ) / κ j) * ‖fderiv ℝ (p j) x‖) ∧
        (∫ x, 1 - χ x ∂μ) ≤
          (∑ i, μ.real {x | d i x < 2 * r i}) + ∑ j, μ.real {x | |p j x| < 2 * κ j} := by
  obtain ⟨A, hA, hLip⟩ := exists_smoothTransition_lipschitz
  obtain ⟨B, hB, hgood⟩ := exists_good_domain_cutoff
  refine ⟨A, hA, B, hB, ?_⟩
  intro I J E _ _ _ _ _ _ _ μ _ d hd hbounded r hr p hp κ hκ
  let b := inequalityBoundaryCutoff r d
  have hdc : ∀ i, Continuous (d i) := fun i => (hd i).continuous
  obtain ⟨χ, hs, hcomp, hrange, hsupp, hone, hder, hloss⟩ := hgood μ
    (positiveInequalityDomain d) b (inequalityBoundaryCutoff_smooth r d hd)
    (inequalityBoundaryCutoff_compact r hr d hdc hbounded) (inequalityBoundaryCutoff_range r d)
    (inequalityBoundaryCutoff_tsupport_domain r hr d hdc) κ hκ p hp
  refine ⟨χ, hs, hcomp, hrange, hsupp, ?_, ?_, ?_⟩
  · intro x hx hpx
    exact hone x (inequalityBoundaryCutoff_eq_one r hr d hx) hpx
  · intro x
    exact (hder x).trans (add_le_add (inequalityBoundaryCutoff_fderiv_norm_le A hLip r hr d hd x) le_rfl)
  · exact hloss.trans (add_le_add (inequalityBoundaryCutoff_integral_loss_le μ r hr d
      (fun i => (hd i).continuous.measurable)) le_rfl)

end Erdos3

end

end OAI
