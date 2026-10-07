/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
import OAI.Combinatorics.Progressions.Probability.WeightedSupportedComplexMixture

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

variable {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]

theorem complexMean_disintegrate_supported (p : FiniteProbabilityWeights X)
    (F : X → R) (f : X → ℂ) :
    p.complexMean f = (p.fiberLaw F).complexMean (fun r =>
      if hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)) then
        (p.condition _ hr).complexMean f else 0) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply p.complexMean_supported_fiber_error F
  intro r hr
  simp only [dite_eq_left hr, sub_self, norm_zero, le_refl]

theorem exists_positive_fiber_ge_complexMean_re (p : FiniteProbabilityWeights X)
    (F : X → R) (f : X → ℂ) :
    ∃ (r : R) (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      (p.complexMean f).re ≤ ((p.condition _ hr).complexMean f).re := by
  rw [p.complexMean_disintegrate_supported F f]
  obtain ⟨r, hr, hv⟩ := (p.fiberLaw F).exists_positive_weight_ge_complexMean_re
    (fun r => if hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r)) then
      (p.condition _ hr).complexMean f else 0)
  rw [p.fiberLaw_weight_eq_mass] at hr
  exact ⟨r, hr, by simpa only [dite_eq_left hr] using hv⟩

omit [DecidableEq X] in
theorem exists_good_ge_complexMean_re_sub_bad [DecidableEq X] (p : FiniteProbabilityWeights X)
    (Good : X → Prop) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ η : ℝ} (hδ : 0 < δ) (hbad : p.eventProbability (fun x => ¬Good x) ≤ η)
    (hlarge : δ + η ≤ (p.complexMean f).re) :
    ∃ x, 0 < p.weight x ∧ Good x ∧ δ ≤ (f x).re := by
  have herr := p.complexMean_goodPart_comparison Good f (fun x _ => f x)
    (show (0 : ℝ) ≤ 0 from le_rfl) hf (fun _ _ => by simp)
  rw [zero_add] at herr
  have hre := (Complex.re_le_norm _).trans (herr.trans hbad)
  rw [Complex.sub_re] at hre
  have hgood : δ ≤ (p.complexMean (fun x => if _ : Good x then f x else 0)).re := by
    linarith only [hre, hlarge]
  obtain ⟨x, hx, hv⟩ := p.exists_positive_weight_ge_complexMean_re
    (fun x => if _ : Good x then f x else 0)
  have hselected := hgood.trans hv
  by_cases hg : Good x
  · exact ⟨x, hx, hg, by simpa only [dite_eq_left hg] using hselected⟩
  · simp only [dite_eq_right hg, Complex.zero_re] at hselected
    exact (not_le_of_gt hδ hselected).elim

end Erdos3.FiniteProbabilityWeights

end

end OAI
