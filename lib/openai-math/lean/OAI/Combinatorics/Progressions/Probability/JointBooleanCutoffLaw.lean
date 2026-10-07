import OAI.Combinatorics.Progressions.Estimates.BooleanCubeGoodTest
import OAI.Combinatorics.Progressions.Probability.SlicedRemainderDensityFamily

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem cutoff_loss_of_density_mass {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] (χ w : X → ℝ)
    (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hwi : Integrable w ν) (hw0 : ∀ x, 0 ≤ w x)
    (hlaw : realDensityMeasure ν w = realDensityMeasure μ χ)
    {η : ℝ} (hmass : 1 - η ≤ ∫ x, w x ∂ν) : (∫ x, 1 - χ x ∂μ) ≤ η := by
  have hi := cutoff_integrable μ χ hχ hχ01
  have hm : (∫ x, χ x ∂μ) = ∫ x, w x ∂ν := by
    rw [← realDensityMeasure_real_univ μ χ hi (fun x => (hχ01 x).1),
      ← hlaw, realDensityMeasure_real_univ ν w hwi hw0]
  rw [integral_sub (integrable_const (1 : ℝ)) hi, hm]
  simpa only [integral_const, probReal_univ, one_smul] using sub_le_iff_le_add.mpr
    (show (1 : ℝ) ≤ η + ∫ x, w x ∂ν by linarith)

theorem density_cutoff_test_error {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] (χ w : X → ℝ)
    (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : Measurable w) (hwi : Integrable w ν) (hw0 : ∀ x, 0 ≤ w x)
    (hlaw : realDensityMeasure ν w = realDensityMeasure μ χ)
    {η : ℝ} (hmass : 1 - η ≤ ∫ x, w x ∂ν)
    (f : X → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    |(∫ x, f x ∂μ) - ∫ x, w x * f x ∂ν| ≤ η := by
  have ht := (mappedTest_cutoff_error μ χ hχ hχ01 id measurable_id f hf hbound).trans
    (cutoff_loss_of_density_mass μ ν χ w hχ hχ01 hwi hw0 hlaw hmass)
  change |(∫ x, f x ∂μ) - ∫ x, f x ∂realDensityMeasure μ χ| ≤ η at ht
  rw [← hlaw, realDensityMeasure_integral ν w hw hw0] at ht
  exact ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

variable {B O J α : Type*} [Fintype B] [Fintype O] [Fintype J] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α]

noncomputable def booleanCubeCutoff (c : J → B → ℝ) (sets : O → Finset α)
    (block : J → O → B) {h : ℕ} (v : Fin h) (sel : J → O → Option α) (ψ : ℝ → ℝ)
    (r : B × Fin h → ℝ) (κ : J → ℝ) (a : BlockParameter B (Fin h) α → ℝ) : ℝ :=
  goodDomainCutoff ψ κ (fun j => booleanCubeDeterminant (c j) sets (block j) v (sel j))
    (scalarCubeProductCutoff α r) ((blockCubeFlatten B (Fin h) α).symm a)

theorem booleanCubeCutoff_contDiff (c : J → B → ℝ) (sets : O → Finset α)
    (block : J → O → B) {h : ℕ} (v : Fin h) (sel : J → O → Option α)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (r : B × Fin h → ℝ) (κ : J → ℝ) :
    ContDiff ℝ ∞ (booleanCubeCutoff c sets block v sel ψ r κ) :=
  (goodDomainCutoff_smooth ψ hψ κ _
    (fun j => booleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j)) _
    (scalarCubeProductCutoff_smooth r)).comp (blockCubeFlatten B (Fin h) α).symm.contDiff

theorem booleanCubeCutoff_range (c : J → B → ℝ) (sets : O → Finset α)
    (block : J → O → B) {h : ℕ} (v : Fin h) (sel : J → O → Option α)
    (ψ : ℝ → ℝ) (hψ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (r : B × Fin h → ℝ) (κ : J → ℝ) (a : BlockParameter B (Fin h) α → ℝ) :
    booleanCubeCutoff c sets block v sel ψ r κ a ∈ Set.Icc (0 : ℝ) 1 :=
  goodDomainCutoff_range ψ hψ κ _ _ (scalarCubeProductCutoff_range r) _

theorem booleanCubeGoodWeight_measure (c : J → B → ℝ) (sets : O → Finset α)
    (block : J → O → B) {h : ℕ} (v : Fin h) (sel : J → O → Option α)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i)
    (κ : J → ℝ) (hκ : ∀ j, 0 < κ j) :
    realDensityMeasure volume (booleanCubeGoodWeight c sets block v sel ψ r κ) =
      realDensityMeasure (blockCubeMeasure B (Fin h) α) (booleanCubeCutoff c sets block v sel ψ r κ) := by
  let w := booleanCubeGoodWeight c sets block v sel ψ r κ
  let χ := booleanCubeCutoff c sets block v sel ψ r κ
  have hw := booleanCubeGoodWeight_spec c sets block v sel ψ hψ hrange hzero r hr κ hκ
  have hm : Measurable χ := (booleanCubeCutoff_contDiff c sets block v sel ψ hψ r κ).continuous.measurable
  have h01 := booleanCubeCutoff_range c sets block v sel ψ hrange r κ
  let : IsFiniteMeasure (realDensityMeasure volume w) :=
    realDensityMeasure_finite volume w (hw.1.continuous.integrable_of_hasCompactSupport hw.2.1) hw.2.2.1
  let : IsFiniteMeasure (realDensityMeasure (blockCubeMeasure B (Fin h) α) χ) :=
    realDensityMeasure_finite _ χ (cutoff_integrable _ χ hm h01) (fun a => (h01 a).1)
  apply finiteMeasure_eq_of_integrals
  intro f _
  rw [realDensityMeasure_integral volume w hw.1.continuous.measurable hw.2.2.1,
    realDensityMeasure_integral _ χ hm (fun a => (h01 a).1), blockCubeMeasure_integral]
  have ht := booleanCubeGoodWeight_integral_test c sets block v sel ψ r hr κ f
  simpa only [χ, booleanCubeCutoff, ContinuousLinearEquiv.symm_apply_apply] using ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

noncomputable def jointBooleanCutoff {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (ψ : ℝ → ℝ)
    (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ) : (JointBlockParameter B h α → ℝ) → ℝ :=
  sigmaAxisWeight (fun d => booleanCubeCutoff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) ψ (r d) (fun _ => κ d))

theorem jointBooleanCutoff_contDiff {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ) :
    ContDiff ℝ 1 (jointBooleanCutoff c sets block v sel ψ r κ) :=
  sigmaAxisWeight_contDiff _ (fun d => (booleanCubeCutoff_contDiff (fun _ : Unit => c d)
    (sets d) (fun _ => block d) (v d) (fun _ => sel d) ψ hψ (r d) (fun _ => κ d)).of_le (by norm_num))

theorem jointBooleanCutoff_range {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (ψ : ℝ → ℝ) (hψ : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ) (x : JointBlockParameter B h α → ℝ) :
    jointBooleanCutoff c sets block v sel ψ r κ x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun d => booleanCubeCutoff_range (fun _ : Unit => c d)
    (sets d) (fun _ => block d) (v d) (fun _ => sel d) ψ hψ (r d) (fun _ => κ d) _)

theorem jointBooleanGoodWeight_measure {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) :
    realDensityMeasure volume (jointBooleanGoodWeight c sets block v sel ψ r κ) =
      realDensityMeasure (jointBooleanSource h) (jointBooleanCutoff c sets block v sel ψ r κ) := by
  let w := fun d => booleanCubeGoodWeight (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) ψ (r d) (fun _ => κ d)
  let χ := fun d => booleanCubeCutoff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) ψ (r d) (fun _ => κ d)
  have hw (d) := booleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) ψ hψ hrange hzero (r d) (hr d) (fun _ => κ d) (fun _ => hκ d)
  have hm (d) : Measurable (χ d) := (booleanCubeCutoff_contDiff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) ψ hψ (r d) (fun _ => κ d)).continuous.measurable
  have h01 (d) := booleanCubeCutoff_range (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) ψ hrange (r d) (fun _ => κ d)
  change realDensityMeasure volume (sigmaAxisWeight w) =
    realDensityMeasure (sigmaAxisMeasure _) (sigmaAxisWeight χ)
  rw [← sigmaAxisMeasure_density w (fun d =>
    (hw d).1.continuous.integrable_of_hasCompactSupport (hw d).2.1) (fun d => (hw d).2.2.1)]
  have hlaw (d) : realDensityMeasure volume (w d) =
      realDensityMeasure (blockCubeMeasure (B d) (Fin (h d)) α) (χ d) :=
    booleanCubeGoodWeight_measure (fun _ : Unit => c d) (sets d) (fun _ => block d)
      (v d) (fun _ => sel d) ψ hψ hrange hzero (r d) (hr d) (fun _ => κ d) (fun _ => hκ d)
  simp_rw [hlaw]
  exact sigmaAxisMeasure_withDensity _ χ (fun d => cutoff_integrable _ _ (hm d) (h01 d))
    (fun d x => (h01 d x).1)

theorem jointBooleanGoodWeight_test_error {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) {η : ℝ}
    (hmass : 1 - η ≤ ∫ x, jointBooleanGoodWeight c sets block v sel ψ r κ x)
    (f : (JointBlockParameter B h α → ℝ) → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) :
    |(∫ x, f x ∂jointBooleanSource h) - ∫ x, jointBooleanGoodWeight c sets block v sel ψ r κ x * f x| ≤ η := by
  have hs := jointBooleanGoodWeight_spec c sets block v sel ψ hψ hrange hzero r hr κ hκ
  exact density_cutoff_test_error _ volume _ _
    (jointBooleanCutoff_contDiff c sets block v sel ψ hψ r κ).continuous.measurable
    (jointBooleanCutoff_range c sets block v sel ψ hrange r κ) hs.1.continuous.measurable
    (hs.1.continuous.integrable_of_hasCompactSupport hs.2.1) hs.2.2.1
    (jointBooleanGoodWeight_measure c sets block v sel ψ hψ hrange hzero r hr κ hκ) hmass f hf hbound

end Erdos3

end

end OAI
