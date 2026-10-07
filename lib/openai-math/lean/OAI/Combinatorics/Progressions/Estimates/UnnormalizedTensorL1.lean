/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracy
import OAI.Combinatorics.Progressions.Probability.SampledWeightCellLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem tensor_density_l1_le_prod_error {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f g : ∀ i, X i → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hg : ∀ i, Integrable (g i) (μ i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hmass : ∀ i, (∫ x, f i x ∂μ i) = 1)
    (ε : I → ℝ) (he : ∀ i, (∫ x, |f i x - g i x| ∂μ i) ≤ ε i) :
    (∫ x, |(∏ i, f i (x i)) - ∏ i, g i (x i)| ∂Measure.pi μ) ≤
      (∏ i, (1 + ε i)) - 1 := by
  let H := fun i x => f i x + |f i x - g i x|
  have hH (i) : Integrable (H i) (μ i) := (hf i).add ((hf i).sub (hg i)).abs
  have hF := Integrable.fintype_prod_dep hf
  have hG := Integrable.fintype_prod_dep hg
  have hHH := Integrable.fintype_prod_dep hH
  have hbound := integral_mono (hF.sub hG).abs (hHH.sub hF)
    (fun x => abs_prod_sub_prod_le_envelope Finset.univ (fun i => f i (x i))
      (fun i => g i (x i)) (fun i _ => hf0 i _) (fun i _ => hg0 i _))
  change (∫ x, |(∏ i, f i (x i)) - ∏ i, g i (x i)| ∂Measure.pi μ) ≤
    ∫ x, (∏ i, H i (x i)) - ∏ i, f i (x i) ∂Measure.pi μ at hbound
  rw [integral_sub hHH hF, integral_fintype_prod_eq_prod, integral_fintype_prod_eq_prod] at hbound
  simp only [hmass, Finset.prod_const_one] at hbound
  refine hbound.trans (sub_le_sub_right ?_ 1)
  apply Finset.prod_le_prod₀
  · intro i _
    exact integral_nonneg (fun x => add_nonneg (hf0 i x) (abs_nonneg _))
  · intro i _
    change (∫ x, f i x + |f i x - g i x| ∂μ i) ≤ 1 + ε i
    have hd : Integrable (fun x => |f i x - g i x|) (μ i) := ((hf i).sub (hg i)).abs
    rw [integral_add (hf i) hd, hmass]
    linarith [he i]

end Erdos3

end

end OAI
