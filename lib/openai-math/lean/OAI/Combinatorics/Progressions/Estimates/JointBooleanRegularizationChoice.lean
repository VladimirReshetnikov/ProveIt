import OAI.Combinatorics.Progressions.Estimates.JointBooleanRegularization
import OAI.Combinatorics.Progressions.Sampling.CubeSamplerGoodRegion

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem exists_joint_boolean_good_region
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (hsets : ∀ d, Function.Injective (sets d)) (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hc : ∀ d o, c₀ d ≤ |c d (block d o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : ∀ d, O d → Option α, ∀ η : D → ℝ, (∀ d, 0 < η d) →
      let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
      let r := fun d (_ : B d × Fin (h d)) =>
        scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
      let w := jointBooleanGoodWeight c sets block (fun d => ⟨0, hh d⟩) sel ψ r κ
      (∀ d, 0 < κ d ∧ κ d ≤ 1 / 2) ∧ ContDiff ℝ 1 w ∧ HasCompactSupport w ∧
        (∀ x, 0 ≤ w x) ∧ 1 - ∑ d, η d ≤ (∫ x, w x) ∧ (∫ x, |w x|) ≤ 1 ∧
        ∀ x ∈ tsupport w, (∀ s, |x s| ≤ 1) ∧ ∀ d, κ d ≤
          |booleanMinorDeterminant (c d) (sets d) (block d) (⟨0, hh d⟩ : Fin (h d))
            (sel d) (fun i => x ⟨d, i⟩)| := by
  classical
  choose sel hsel using fun d => exists_cube_sampler_good_region
    (fun _ : Unit => c d) (sets d) (hsets d) (h d) (hh d) (hcard d)
    (fun _ => block d) (fun _ => hblock d) (hc₀ d) (fun _ => hc d)
    ψ hψ hrange hzero hone
  refine ⟨fun d => sel d (), ?_⟩
  intro η hη
  let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
  let r := fun d (_ : B d × Fin (h d)) =>
    scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
  let w := fun d => booleanCubeGoodWeight (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (⟨0, hh d⟩ : Fin (h d)) (fun _ => sel d ()) ψ (r d) (fun _ => κ d)
  have he (d : D) : sel d = fun _ => sel d () := by
    funext u
    cases u
    rfl
  have hm (d : D) : 1 - η d ≤ ∫ a, w d a := by
    have ht := hsel d (η d) (hη d)
    rw [he d] at ht
    exact ht.2.2.2.2.2.1
  have hκ (d : D) : 0 < κ d := canonicalCubeMinorThreshold_pos Unit (O d) α (hh d) (hc₀ d) (hη d)
  have hr (d : D) (i : B d × Fin (h d)) : 0 < r d i :=
    scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d))
  have haxis (d : D) := booleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (⟨0, hh d⟩ : Fin (h d)) (fun _ => sel d ()) ψ hψ hrange hzero
    (r d) (hr d) (fun _ => κ d) (fun _ => hκ d)
  have hu (d : D) : (∫ a, w d a) ≤ 1 := by
    have hn (a) : |w d a| = w d a := abs_of_nonneg ((haxis d).2.2.1 a)
    have ht : (∫ a, |w d a|) ≤ 1 := (haxis d).2.2.2.1
    simpa only [hn] using ht
  have hs := jointBooleanGoodWeight_spec c sets block (fun d => ⟨0, hh d⟩)
    (fun d => sel d ()) ψ hψ hrange hzero r hr κ hκ
  refine ⟨fun d => ⟨hκ d, canonicalCubeMinorThreshold_le_half Unit (O d) α (hh d) (hc₀ d) (hη d)⟩,
    hs.1, hs.2.1, hs.2.2.1, ?_, hs.2.2.2.1, hs.2.2.2.2⟩
  exact sigmaAxisWeight_mass_loss w (fun d => (haxis d).2.2.1) hu η hm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem exists_joint_boolean_good_region_with_tests
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (hsets : ∀ d, Function.Injective (sets d)) (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hc : ∀ d o, c₀ d ≤ |c d (block d o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : ∀ d, O d → Option α, ∀ η : D → ℝ, (∀ d, 0 < η d) →
      let κ := fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d)
      let r := fun d (_ : B d × Fin (h d)) =>
        scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
      let w := jointBooleanGoodWeight c sets block (fun d => ⟨0, hh d⟩) sel ψ r κ
      (∀ d, 0 < κ d ∧ κ d ≤ 1 / 2) ∧ ContDiff ℝ 1 w ∧ HasCompactSupport w ∧
        (∀ x, 0 ≤ w x) ∧ 1 - ∑ d, η d ≤ (∫ x, w x) ∧ (∫ x, |w x|) ≤ 1 ∧
        (∀ x ∈ tsupport w, (∀ s, |x s| ≤ 1) ∧ ∀ d, κ d ≤
          |booleanMinorDeterminant (c d) (sets d) (block d) (⟨0, hh d⟩ : Fin (h d))
            (sel d) (fun i => x ⟨d, i⟩)|) ∧
        ∀ f : (JointBlockParameter B h α → ℝ) → ℝ, Measurable f → (∀ x, ‖f x‖ ≤ 1) →
          |(∫ x, f x ∂jointBooleanSource h) - ∫ x, w x * f x| ≤ ∑ d, η d := by
  obtain ⟨sel, hsel⟩ := exists_joint_boolean_good_region c sets hsets h hh hcard block hblock
    c₀ hc₀ hc ψ hψ hrange hzero hone
  refine ⟨sel, ?_⟩
  intro η hη
  obtain ⟨hκ, hw, hs, hn, hm, ha, hsupport⟩ := hsel η hη
  refine ⟨hκ, hw, hs, hn, hm, ha, hsupport, ?_⟩
  intro f hf hb
  exact jointBooleanGoodWeight_test_error c sets block (fun d => ⟨0, hh d⟩) sel ψ hψ hrange hzero
    _ (fun d _ => scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d)))
    _ (fun d => (hκ d).1) hm f hf hb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def jointBooleanRegularizationBudget {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (c₀ C : D → ℝ) (A T : ℝ≥0) (η : D → ℝ) : ℝ≥0 :=
  jointBooleanTranslationBudget (B := B) (O := O) (α := α) h C A T
    (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2))
    (fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d))

theorem jointBoolean_regularization_choice_error {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (sets : ∀ d, O d → Finset α)
    (hsets : ∀ d, Function.Injective (sets d)) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (c : ∀ d, B d → ℝ) (hclow : ∀ d o, c₀ d ≤ |c d (block d o)|)
    (hcup : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (η : D → ℝ) (hη : ∀ d, 0 < η d) (δ : ℝ≥0) (hδ : 0 < δ)
    (φ : ((Σ d, O d) → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, regularizedImageDensity (jointBooleanSource h) (jointBooleanSampler h c sets) δ x*φ x) -
      mappedTest (jointBooleanSource h) (jointBooleanSampler h c sets) φ| ≤
      2*(∑ d, η d)+jointBooleanRegularizationBudget (B := B) (O := O) (α := α) h c₀ C A T η*δ := by
  obtain ⟨sel, hs⟩ := exists_joint_boolean_good_region c sets hsets h hh hcard block hblock c₀ hc₀ hclow
    ψ hψ hrange hzero hone
  have hgood := hs η hη
  exact jointBoolean_regularization_error h c sets block hblock (fun d => ⟨0, hh d⟩) sel hcard C hC hcup
    ψ hψ hrange hzero A T hLip hTransition
    (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2))
    (fun d _ => scalarCubeProductBoundaryRadius_pos (B d × Fin (h d)) α (half_pos (hη d)))
    (fun d => canonicalCubeMinorThreshold Unit (O d) α (h d) (c₀ d) (η d))
    (fun d => (hgood.1 d).1) hgood.2.2.2.2.1 δ hδ φ hφ hbound

end Erdos3

end

end OAI
