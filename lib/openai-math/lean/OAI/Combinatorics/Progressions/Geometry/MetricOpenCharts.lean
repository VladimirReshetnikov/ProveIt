import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_openPartialHomeomorph_of_metric_bounds
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Nonempty X]
    (f : X → Y) (hf : Continuous f) (ho : IsOpenMap f) (U : Set X) (hU : IsOpen U) (K : ℝ≥0)
    (hupper : ∀ x ∈ U, ∀ y ∈ U, dist (f x) (f y) ≤ K * dist x y)
    (hlower : ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ K * dist (f x) (f y)) :
    ∃ e : OpenPartialHomeomorph X Y, (∀ x, e x = f x) ∧ e.source = U ∧ e.target = f '' U ∧
      LipschitzOnWith K e e.source ∧ LipschitzOnWith K e.symm e.target := by
  have hinj : Set.InjOn f U := by
    intro x hx y hy hxy
    apply dist_eq_zero.mp
    exact le_antisymm (by simpa only [hxy, dist_self, mul_zero] using hlower x hx y hy) dist_nonneg
  let e := OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv f U) hf.continuousOn ho hU
  refine ⟨e, fun _ => rfl, rfl, rfl, ?_, ?_⟩
  · exact LipschitzOnWith.of_dist_le_mul hupper
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hlower (e.symm x) (e.map_target hx) (e.symm y) (e.map_target hy)
    change dist (e.symm x) (e.symm y) ≤ K * dist (e (e.symm x)) (e (e.symm y)) at h
    simpa only [e.right_inv hx, e.right_inv hy] using h

end Erdos3

end

end OAI
