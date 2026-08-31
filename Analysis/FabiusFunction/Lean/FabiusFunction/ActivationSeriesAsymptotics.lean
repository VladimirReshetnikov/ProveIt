import FabiusFunction.ActivationAsymptotics
import FabiusFunction.ActivationSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Sharp asymptotics for square-summable activation series

The one-coordinate limit

`activationProbability (a * t) / t ^ 2 -> a ^ 2 / 3`

extends to every square-summable real weight family.  Tannery's theorem
interchanges the limit and the topological sum, while the global estimate

`activationProbability x ≤ x ^ 2 / 3`

provides the same summable majorant as the limiting coefficient.  Thus no
Taylor remainder or finite-support approximation is needed, and the global
budget from `FabiusFunction.ActivationSeries` is coefficient-sharp.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Fabius

noncomputable section

/-- For every square-summable real weight family, the sum of the activation
probabilities has sharp quadratic coefficient one third of the squared
`ℓ²` norm:

`(∑' i, activationProbability (w i * t)) / t ^ 2
    -> (∑' i, w i ^ 2) / 3`

as `t -> 0` through nonzero values.  The index type is arbitrary; the
summability hypothesis itself supplies all countability needed by `tsum`. -/
theorem tendsto_tsum_activationProbability_mul_div_sq
    {ι : Type*} {w : ι → ℝ} (hw : Summable (fun i ↦ w i ^ 2)) :
    Tendsto
      (fun t : ℝ ↦
        (∑' i : ι, activationProbability (w i * t)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 ((∑' i : ι, w i ^ 2) / 3)) := by
  have hlimit :
      Tendsto
        (fun t : ℝ ↦
          ∑' i : ι, activationProbability (w i * t) / t ^ 2)
        (𝓝[≠] 0) (𝓝 (∑' i : ι, w i ^ 2 / 3)) := by
    refine tendsto_tsum_of_dominated_convergence
      (hw.div_const 3)
      (fun i ↦ tendsto_activationProbability_mul_div_sq (w i)) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht i
    have ht0 : t ≠ 0 := by simpa using ht
    rw [Real.norm_of_nonneg
      (div_nonneg (activationProbability_nonneg (w i * t)) (sq_nonneg t))]
    apply (div_le_iff₀ (sq_pos_of_ne_zero ht0)).2
    calc
      activationProbability (w i * t) ≤ (t ^ 2 / 3) * w i ^ 2 :=
        activationProbability_mul_le_quadratic (w i) t
      _ = (w i ^ 2 / 3) * t ^ 2 := by ring

  simpa only [tsum_div_const] using hlimit

end

end Fabius
