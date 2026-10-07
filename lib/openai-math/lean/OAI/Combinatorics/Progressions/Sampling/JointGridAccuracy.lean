import OAI.Combinatorics.Progressions.Estimates.FiniteImageProducts
import OAI.Combinatorics.Progressions.Geometry.CommonSupportRadius

namespace OAI

section

namespace Erdos3

open scoped BigOperators

instance oddTorusFactor_neZero (Q : ℕ) : NeZero (2 * Q + 1) := ⟨by omega⟩

theorem jointImageMass_eq_grid_product {D : Type*} [Fintype D] [DecidableEq D]
    {X J : D → Type*} [∀ d, Fintype (X d)] [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → J d → ℤ)
    (H : D → ℝ) (K : D → ℕ) (hK : ∀ d, 0 < K d) (hH : ∀ d, 0 ≤ H d)
    (center z : ∀ d, J d → ℤ)
    (hY : ∀ d x, (p d).weight x ≠ 0 → ∀ j, |(Y d x j : ℝ) - center d j| ≤ H d * K d)
    (hz : ∀ d, centeredFundamentalBox (commonSupportRadius H) (K d) (center d) (z d)) :
    (∏ d, (K d : ℝ) ^ Fintype.card (J d)) *
      finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z =
        ∏ d, integerGridDensity (p d) (Y d) (K d) ((2 * commonSupportRadius H + 1) * K d) (z d) := by
  rw [scaledImageMass_pi]
  apply Finset.prod_congr rfl
  intro d _
  exact (integerGridDensity_eq_imageMass_on_centered_box (p d) (Y d) (center d) (z d)
    (hK d) (commonSupportRadius_le H hH d) (hY d) (hz d)).symm

theorem jointImageMass_at_representatives {D : Type*} [Fintype D] [DecidableEq D]
    {X J : D → Type*} [∀ d, Fintype (X d)] [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → J d → ℤ)
    (H : D → ℝ) (K : D → ℕ) (hK : ∀ d, 0 < K d) (hH : ∀ d, 0 ≤ H d)
    (center : ∀ d, J d → ℤ)
    (hY : ∀ d x, (p d).weight x ≠ 0 → ∀ j, |(Y d x j : ℝ) - center d j| ≤ H d * K d)
    (r : ∀ d, J d → ZMod ((2 * commonSupportRadius H + 1) * K d)) :
    (∏ d, (K d : ℝ) ^ Fintype.card (J d)) * finiteImageMass (FiniteProbabilityWeights.pi p)
      (fun x d => Y d (x d)) (fun d => centeredGridRepresentative (commonSupportRadius H) (K d) (center d) (r d)) =
        ∏ d, integerGridDensity (p d) (Y d) (K d) ((2 * commonSupportRadius H + 1) * K d)
          (centeredGridRepresentative (commonSupportRadius H) (K d) (center d) (r d)) :=
  jointImageMass_eq_grid_product p Y H K hK hH center _ hY
    (fun d => centeredGridRepresentative_mem _ _ (hK d) _ _)

theorem jointGridDensity_total {D : Type*} [Fintype D] [DecidableEq D]
    {X J : D → Type*} [∀ d, Fintype (X d)] [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → J d → ℤ)
    (Q : ℕ) (K : D → ℕ) [∀ d, NeZero (K d)] (center : ∀ d, J d → ℤ) :
    (∑ r : ∀ d, J d → ZMod ((2 * Q + 1) * K d), ∏ d,
      integerGridDensity (p d) (Y d) (K d) ((2 * Q + 1) * K d)
        (centeredGridRepresentative Q (K d) (center d) (r d))) =
      ∏ d, (K d : ℝ) ^ Fintype.card (J d) := by
  rw [← Fintype.prod_sum (fun d (r : J d → ZMod ((2 * Q + 1) * K d)) =>
    integerGridDensity (p d) (Y d) (K d) ((2 * Q + 1) * K d)
      (centeredGridRepresentative Q (K d) (center d) r))]
  apply Finset.prod_congr rfl
  intro d _
  exact integerGridDensity_total (p d) (Y d) (K d) ((2 * Q + 1) * K d) _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def jointGridAxisTolerance (d : ℕ) (C ε : ℝ) : ℝ := ε / (d * C ^ d + 1)

theorem jointGridAxisTolerance_spec (d : ℕ) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    0 < jointGridAxisTolerance d C ε ∧ jointGridAxisTolerance d C ε ≤ ε ∧
      d * jointGridAxisTolerance d C ε * C ^ d ≤ ε := by
  have ha : 0 ≤ (d : ℝ) * C ^ d := by positivity
  have hp : 0 < (d : ℝ) * C ^ d + 1 := by linarith
  have hpos : 0 < jointGridAxisTolerance d C ε := div_pos hε hp
  refine ⟨hpos, div_le_self hε.le (by linarith), ?_⟩
  have he : ((d : ℝ) * C ^ d + 1) * jointGridAxisTolerance d C ε = ε := by
    unfold jointGridAxisTolerance
    field_simp
  nlinarith only [he, hpos]

theorem joint_integer_density_approximation {D : Type*} [Fintype D] [DecidableEq D]
    {X J : D → Type*} [∀ d, Fintype (X d)] [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)]
    (p : ∀ d, FiniteProbabilityWeights (X d)) (Y : ∀ d, X d → J d → ℤ)
    (H : D → ℝ) (K : D → ℕ) (hK : ∀ d, 0 < K d) (hH : ∀ d, 0 ≤ H d)
    (center z : ∀ d, J d → ℤ)
    (hY : ∀ d x, (p d).weight x ≠ 0 → ∀ j, |(Y d x j : ℝ) - center d j| ≤ H d * K d)
    (hz : ∀ d, centeredFundamentalBox (commonSupportRadius H) (K d) (center d) (z d))
    (f : D → ℂ) {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε)
    (hcap : ∀ d, ‖(integerGridDensity (p d) (Y d) (K d)
      ((2 * commonSupportRadius H + 1) * K d) (z d) : ℂ)‖ ≤ C)
    (hfcap : ∀ d, ‖f d‖ ≤ C)
    (herror : ∀ d, ‖(integerGridDensity (p d) (Y d) (K d)
      ((2 * commonSupportRadius H + 1) * K d) (z d) : ℂ) - f d‖ ≤
        jointGridAxisTolerance (Fintype.card D) C ε) :
    ‖(((∏ d, (K d : ℝ) ^ Fintype.card (J d)) *
      finiteImageMass (FiniteProbabilityWeights.pi p) (fun x d => Y d (x d)) z : ℝ) : ℂ) - ∏ d, f d‖ ≤ ε := by
  have hid (d) := integerGridDensity_eq_imageMass_on_centered_box (p d) (Y d) (center d) (z d)
    (hK d) (commonSupportRadius_le H hH d) (hY d) (hz d)
  have hs := jointGridAxisTolerance_spec (Fintype.card D) (le_trans (by norm_num) hC) hε
  have ht := scaledImageMass_pi_approximation p Y z (fun d => (K d : ℝ) ^ Fintype.card (J d))
    f hC hs.1.le (fun d => by simpa only [hid d] using hcap d) hfcap
    (fun d => by simpa only [hid d] using herror d)
  exact ht.trans hs.2.2

end Erdos3

end

end OAI
