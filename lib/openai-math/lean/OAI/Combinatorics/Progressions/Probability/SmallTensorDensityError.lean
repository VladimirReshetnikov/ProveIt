/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Analysis.Complex.Exponential
import OAI.Combinatorics.Progressions.Estimates.UnnormalizedTensorL1

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem prod_one_add_error_le_exp {I : Type*} [Fintype I]
    (ε : I → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    (∏ i, (1 + ε i)) ≤ Real.exp (∑ i, ε i) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ => by linarith [hε i])
    (fun i _ => by simpa only [add_comm] using Real.add_one_le_exp (ε i))

theorem tensor_density_l1_le_twice_sum {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f g : ∀ i, X i → ℝ) (hf : ∀ i, Integrable (f i) (μ i))
    (hg : ∀ i, Integrable (g i) (μ i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hmass : ∀ i, (∫ x, f i x ∂μ i) = 1)
    (ε : I → ℝ) (he : ∀ i, (∫ x, |f i x - g i x| ∂μ i) ≤ ε i)
    (hsmall : (∑ i, ε i) ≤ 1) :
    (∫ x, |(∏ i, f i (x i)) - ∏ i, g i (x i)| ∂Measure.pi μ) ≤ 2 * ∑ i, ε i := by
  have hε (i) : 0 ≤ ε i := (integral_nonneg (fun _ => abs_nonneg _)).trans (he i)
  have hsum : 0 ≤ ∑ i, ε i := Finset.sum_nonneg (fun i _ => hε i)
  have hexp := Real.abs_exp_sub_one_le (x := ∑ i, ε i)
    (by simpa only [abs_of_nonneg hsum] using hsmall)
  rw [abs_of_nonneg hsum] at hexp
  exact (tensor_density_l1_le_prod_error μ f g hf hg hf0 hg0 hmass ε he).trans
    ((sub_le_sub_right (prod_one_add_error_le_exp ε hε) 1).trans
      ((le_abs_self _).trans hexp))

end Erdos3

end

end OAI
