import FabiusFunction.HyperbolicActivation
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Square-summable activation series

The global one-coordinate estimate

`activationProbability x ≤ x ^ 2 / 3`

lifts directly to every square-summable real weight family.  This module
packages the resulting summability and exact quadratic budget independently
of any particular geometric lattice.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-- Rescaling the field by `a` rescales the global quadratic activation budget
by `a ^ 2`. -/
theorem activationProbability_mul_le_quadratic (a t : ℝ) :
    activationProbability (a * t) ≤ (t ^ 2 / 3) * a ^ 2 := by
  calc
    activationProbability (a * t) ≤ (a * t) ^ 2 / 3 :=
      activationProbability_le_sq_div_three _
    _ = (t ^ 2 / 3) * a ^ 2 := by ring

/-- Activation probabilities sampled along a square-summable real weight
family form a summable series at every field parameter. -/
theorem summable_activationProbability_mul_of_summable_sq
    {ι : Type*} {w : ι → ℝ} (hw : Summable (fun i ↦ w i ^ 2)) (t : ℝ) :
    Summable (fun i : ι ↦ activationProbability (w i * t)) := by
  have hmajor : Summable (fun i : ι ↦ (t ^ 2 / 3) * w i ^ 2) :=
    hw.mul_left (t ^ 2 / 3)
  exact Summable.of_nonneg_of_le
    (fun i ↦ activationProbability_nonneg (w i * t))
    (fun i ↦ activationProbability_mul_le_quadratic (w i) t)
    hmajor

/-- The total activation of a square-summable weight family is bounded by
one third of its squared `ℓ²` norm times the squared field:

`∑' i, activationProbability (w i * t)
    ≤ (t ^ 2 / 3) * ∑' i, w i ^ 2`. -/
theorem tsum_activationProbability_mul_le
    {ι : Type*} {w : ι → ℝ} (hw : Summable (fun i ↦ w i ^ 2)) (t : ℝ) :
    (∑' i : ι, activationProbability (w i * t)) ≤
      (t ^ 2 / 3) * ∑' i : ι, w i ^ 2 := by
  have hterms := summable_activationProbability_mul_of_summable_sq hw t
  have hmajor : Summable (fun i : ι ↦ (t ^ 2 / 3) * w i ^ 2) :=
    hw.mul_left (t ^ 2 / 3)
  calc
    (∑' i : ι, activationProbability (w i * t)) ≤
        ∑' i : ι, (t ^ 2 / 3) * w i ^ 2 :=
      hterms.tsum_le_tsum
        (fun i ↦ activationProbability_mul_le_quadratic (w i) t)
        hmajor
    _ = (t ^ 2 / 3) * ∑' i : ι, w i ^ 2 := by
      rw [tsum_mul_left]

end

end Fabius
