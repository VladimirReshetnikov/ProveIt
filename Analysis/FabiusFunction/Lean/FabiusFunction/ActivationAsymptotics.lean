import FabiusFunction.HyperbolicActivation
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.LHopital

/-!
# Sharp local asymptotics of the activation probability

The global estimate

`activationProbability x <= x ^ 2 / 3`

from `FabiusFunction.HyperbolicActivation` has the best possible quadratic
coefficient.  This module proves that fact in its most transparent form:

`activationProbability x / x ^ 2 -> 1 / 3`

as `x` tends to zero through nonzero values.

The proof applies l'Hopital's rule once to

`(x - tanh x) / x ^ 3`.

Its derivative quotient is `(tanh x / x) ^ 2 / 3`, whose limit is immediate
from the continuous totalization `tanhDiv 0 = 1`.  Thus the proof reuses the
removable-quotient API instead of introducing a separate Taylor expansion.
An arbitrary real dilation then multiplies the coefficient by its square;
the zero dilation is included explicitly for later use with sparse weight
families.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Fabius

noncomputable section

/-- The activation probability has sharp quadratic coefficient `1 / 3` at
the origin:

`activationProbability x / x ^ 2 -> 1 / 3`

as `x -> 0` through nonzero values. -/
theorem tendsto_activationProbability_div_sq :
    Tendsto (fun x : ℝ ↦ activationProbability x / x ^ 2)
      (𝓝[≠] 0) (𝓝 (1 / 3 : ℝ)) := by
  have hf (x : ℝ) :
      HasDerivAt (fun y : ℝ ↦ y - Real.tanh y)
        (Real.tanh x ^ 2) x := by
    apply ((hasDerivAt_id x).sub (hasDerivAt_tanh x)).congr_deriv
    ring

  have hg (x : ℝ) :
      HasDerivAt (fun y : ℝ ↦ y ^ 3) (3 * x ^ 2) x := by
    apply (hasDerivAt_pow 3 x).congr_deriv
    norm_num

  have hg_ne :
      ∀ᶠ x : ℝ in 𝓝[≠] 0, 3 * x ^ 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hx0)

  have htanhDiv : Tendsto tanhDiv (𝓝[≠] 0) (𝓝 1) := by
    have hc : ContinuousAt tanhDiv 0 :=
      continuous_tanhDiv.continuousAt
    have hfull : Tendsto tanhDiv (𝓝 (0 : ℝ)) (𝓝 1) := by
      simpa only [tanhDiv_zero] using hc.tendsto
    exact hfull.mono_left nhdsWithin_le_nhds

  have hderivativeQuotient :
      Tendsto
        (fun x : ℝ ↦ Real.tanh x ^ 2 / (3 * x ^ 2))
        (𝓝[≠] 0) (𝓝 (1 / 3 : ℝ)) := by
    have hlim :
        Tendsto (fun x : ℝ ↦ tanhDiv x ^ 2 / 3)
          (𝓝[≠] 0) (𝓝 (1 / 3 : ℝ)) := by
      simpa using (htanhDiv.pow 2).div_const (3 : ℝ)
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    rw [tanhDiv_of_ne_zero hx0]
    field_simp [hx0]

  have hnumerator :
      Tendsto (fun x : ℝ ↦ x - Real.tanh x) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (hf 0).continuousAt.mono_left
      nhdsWithin_le_nhds

  have hdenominator :
      Tendsto (fun x : ℝ ↦ x ^ 3) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (hg 0).continuousAt.mono_left nhdsWithin_le_nhds

  have hquotient :
      Tendsto
        (fun x : ℝ ↦ (x - Real.tanh x) / x ^ 3)
        (𝓝[≠] 0) (𝓝 (1 / 3 : ℝ)) :=
    HasDerivAt.lhopital_zero_nhdsNE
      (Eventually.of_forall hf)
      (Eventually.of_forall hg)
      hg_ne hnumerator hdenominator hderivativeQuotient

  apply hquotient.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  rw [activationProbability_of_ne_zero hx0]
  field_simp [hx0]

/-- Scaling the field by `a` scales the sharp quadratic activation
coefficient by `a ^ 2`:

`activationProbability (a * x) / x ^ 2 -> a ^ 2 / 3`

as `x -> 0` through nonzero values.  The statement includes `a = 0`, so it
can be applied termwise to weight families with vanishing coordinates. -/
theorem tendsto_activationProbability_mul_div_sq (a : ℝ) :
    Tendsto (fun x : ℝ ↦ activationProbability (a * x) / x ^ 2)
      (𝓝[≠] 0) (𝓝 (a ^ 2 / 3)) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp

  have hscale :
      Tendsto (fun x : ℝ ↦ a * x) (𝓝[≠] 0) (𝓝[≠] 0) := by
    simpa using
      (hasDerivAt_const_mul (x := (0 : ℝ)) a).tendsto_nhdsNE ha

  have hscaled :=
    (tendsto_activationProbability_div_sq.comp hscale).mul_const (a ^ 2)
  have htarget :
      Tendsto (fun x : ℝ ↦ activationProbability (a * x) / x ^ 2)
        (𝓝[≠] 0) (𝓝 ((1 / 3 : ℝ) * a ^ 2)) := by
    apply hscaled.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    simp only [Function.comp_apply]
    field_simp [ha, hx0]
  convert htarget using 1
  ring_nf

end

end Fabius
