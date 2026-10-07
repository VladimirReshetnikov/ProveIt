import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.Span.Basic

namespace OAI

section

namespace Erdos3

theorem exists_list_sum_of_mem_span {R V : Type*} [Semiring R]
    [AddCommMonoid V] [Module R V] (S : Set V)
    (hsmul : ∀ r : R, ∀ x ∈ S, r • x ∈ S) {v : V} (hv : v ∈ Submodule.span R S) :
    ∃ xs : List V, (∀ x ∈ xs, x ∈ S) ∧ xs.sum = v := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨[x], by simpa using hx, by simp⟩
  | zero => exact ⟨[], by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨xs, hxs, ex⟩ := hx
    obtain ⟨ys, hys, ey⟩ := hy
    refine ⟨xs ++ ys, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hxs z hz
      · exact hys z hz
    · simp only [List.sum_append, ex, ey]
  | smul r x _ hx =>
    obtain ⟨xs, hxs, ex⟩ := hx
    refine ⟨xs.map (fun y => r • y), ?_, ?_⟩
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      exact hsmul r y (hxs y hy)
    · rw [← ex]
      clear hxs ex
      induction xs with
      | nil => simp
      | cons y ys ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

end Erdos3

end

end OAI
