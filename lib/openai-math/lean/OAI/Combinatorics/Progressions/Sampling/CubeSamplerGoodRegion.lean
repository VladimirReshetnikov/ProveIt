import OAI.Combinatorics.Progressions.Estimates.BooleanCubeGoodTest
import OAI.Combinatorics.Progressions.Estimates.CanonicalCubeMinorThreshold

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

theorem exists_cube_sampler_good_region {B O J α : Type*}
    [Fintype B] [Fintype O] [Nonempty O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : J → O → B) (hblock : ∀ j, Function.Injective (block j))
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ j o, c₀ ≤ |c j (block j o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : J → O → Option α, ∀ η : ℝ, 0 < η →
      let κ := canonicalCubeMinorThreshold J O α h c₀ η
      let r := fun _ : B × Fin h => scalarCubeProductBoundaryRadius (B × Fin h) α (η / 2)
      let w := booleanCubeGoodWeight c sets block (⟨0, hh⟩ : Fin h) sel ψ r (fun _ => κ)
      0 < κ ∧ κ ≤ 1 / 2 ∧ ContDiff ℝ 1 w ∧ HasCompactSupport w ∧
        (∀ a, 0 ≤ w a) ∧ 1 - η ≤ (∫ a, w a) ∧ (∫ a, |w a|) ≤ 1 ∧
        (∀ a ∈ tsupport w, (∀ z, |a z| ≤ 1) ∧
          ∀ j, κ ≤ |booleanMinorDeterminant (c j) sets (block j) (⟨0, hh⟩ : Fin h) (sel j) a|) ∧
        ∀ f : (BlockParameter B (Fin h) α → ℝ) → ℝ, Measurable f → (∀ a, ‖f a‖ ≤ 1) →
          |(∫ a, f a ∂blockCubeMeasure B (Fin h) α) - ∫ a, w a * f a| ≤ η := by
  obtain ⟨sel, hsel⟩ := exists_canonical_cube_minor_thresholds c sets hsets h hh hcard block hblock hc₀ hc
  refine ⟨sel, ?_⟩
  intro η hη
  let κ := canonicalCubeMinorThreshold J O α h c₀ η
  let r := fun _ : B × Fin h => scalarCubeProductBoundaryRadius (B × Fin h) α (η / 2)
  have hκ : 0 < κ := canonicalCubeMinorThreshold_pos J O α hh hc₀ hη
  have hκhalf : κ ≤ 1 / 2 := canonicalCubeMinorThreshold_le_half J O α hh hc₀ hη
  have hr : ∀ i, 0 < r i := fun _ => scalarCubeProductBoundaryRadius_pos (B × Fin h) α (half_pos hη)
  have hs := booleanCubeGoodWeight_spec c sets block (⟨0, hh⟩ : Fin h) sel ψ hψ hrange hzero
    r hr (fun _ => κ) (fun _ => hκ)
  have hmass := booleanCubeGoodWeight_mass_error c sets block (⟨0, hh⟩ : Fin h) sel ψ hψ hrange hone
    (fun _ => κ) (fun _ => hκ) hη (hsel η hη)
  refine ⟨hκ, hκhalf, hs.1, hs.2.1, hs.2.2.1, hmass, hs.2.2.2.1, hs.2.2.2.2, ?_⟩
  intro f hf hbound
  have ht := booleanCubeGoodWeight_test_error c sets block (⟨0, hh⟩ : Fin h) sel ψ hψ hrange hone
    r hr (fun _ => κ) (fun _ => hκ) f hf hbound
  have hb := scalarCubeProductBoundaryRadius_loss (B × Fin h) α (half_pos hη)
  have hp := hsel η hη
  exact ht.trans (by dsimp only [r, κ] at ht ⊢; linarith)

end Erdos3

end

end OAI
