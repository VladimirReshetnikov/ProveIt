/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

namespace OAI

section

namespace Erdos3

theorem finite_cover_inside_image {X Y I : Type*} [Nonempty X] [PseudoMetricSpace Y]
    (f : X → Y) (c : I → Y) {δ : ℝ} (hcover : ∀ x, ∃ i, dist (f x) (c i) ≤ δ) :
    ∃ a : I → X, ∀ x, ∃ i, dist (f x) (f (a i)) ≤ 2 * δ := by
  classical
  let a : I → X := fun i => if h : ∃ x, dist (f x) (c i) ≤ δ then Classical.choose h
    else Classical.ofNonempty
  have ha (i : I) (h : ∃ x, dist (f x) (c i) ≤ δ) : dist (f (a i)) (c i) ≤ δ := by
    simpa only [a, dite_eq_left h] using Classical.choose_spec h
  refine ⟨a, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  refine ⟨i, (dist_triangle (f x) (c i) (f (a i))).trans ?_⟩
  rw [dist_comm (c i)]
  linarith [ha i ⟨x, hi⟩]

end Erdos3

end

end OAI
