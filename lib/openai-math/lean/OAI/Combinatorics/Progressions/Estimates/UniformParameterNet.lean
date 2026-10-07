/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Sampling.NormalizedRealBoxHalfGrid

namespace OAI

section

namespace Erdos3

theorem exists_uniform_parameter_net {J Ω : Type*} [Fintype J] [Nonempty Ω]
    (f : Ω → J → ℝ) {B : ℝ} (hB : 0 < B) (hf : ∀ x j, |f x j| ≤ B)
    {N : ℕ} (hN : 0 < N) :
    ∃ (code : Ω → J → Fin (N + 1)) (rep : (J → Fin (N + 1)) → Ω),
      ∀ x, dist (f x) (f (rep (code x))) ≤ 4 * B / N := by
  classical
  choose code hcode using fun x => exists_uniformBoxGrid_approx hB hN (f x) (hf x)
  let rep : (J → Fin (N + 1)) → Ω := fun i =>
    if h : ∃ x, code x = i then h.choose else Classical.choice inferInstance
  have hrep (x : Ω) : code (rep (code x)) = code x := by
    have h : ∃ y, code y = code x := ⟨x, rfl⟩
    simp only [rep, dite_eq_left h]
    exact h.choose_spec
  refine ⟨code, rep, fun x => ?_⟩
  calc
    dist (f x) (f (rep (code x))) ≤
        dist (f x) (uniformBoxGrid B N (code x)) +
          dist (uniformBoxGrid B N (code x)) (f (rep (code x))) := dist_triangle _ _ _
    _ ≤ 2 * B / N + 2 * B / N := by
      apply add_le_add (hcode x)
      have hr := hcode (rep (code x))
      rw [hrep x] at hr
      exact (dist_comm _ _).trans_le hr
    _ = _ := by ring

end Erdos3

end

end OAI
