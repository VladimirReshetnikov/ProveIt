import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.Algebra.Support

namespace OAI

section

namespace Erdos3

open scoped Topology

theorem continuous_mul_of_local_right {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : Continuous f)
    (hg : ∀ x ∈ tsupport f, ContinuousAt g x) : Continuous (fun x => f x * g x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.continuousAt.mul (hg x hx)
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (continuousAt_const (y := (0 : ℝ))).congr
    filter_upwards [hz] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

end Erdos3

end

end OAI
