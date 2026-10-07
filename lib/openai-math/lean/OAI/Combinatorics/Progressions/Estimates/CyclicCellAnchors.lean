/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.InteriorIntervalCutoff

namespace OAI

section

namespace Erdos3

theorem exists_cyclic_cell_anchors {I : Type*} (N : ℕ) [NeZero N]
    (A : I → ZMod N → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcircle : ∀ i x y, 0 < A i x → 0 < A i y →
      dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) :
    ∃ anchor : I → ZMod N → ℝ,
      (∀ i h, |anchor i h| ≤ N) ∧
      ∀ i h x, x ∉ cyclicWrapExceptional h ρ → 0 < A i x →
        |(x.val : ℝ) - anchor i h| ≤ (N : ℝ) * ρ := by
  classical
  let pick (i : I) (h : ZMod N) : ZMod N :=
    if hx : ∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x then hx.choose else 0
  have hpick (i : I) (h : ZMod N)
      (hx : ∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x) :
      pick i h ∉ cyclicWrapExceptional h ρ ∧ 0 < A i (pick i h) := by
    simpa only [pick, dite_eq_left hx] using hx.choose_spec
  refine ⟨fun i h => ((pick i h).val : ℝ), ?_, ?_⟩
  · intro i h
    change |((pick i h).val : ℝ)| ≤ (N : ℝ)
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.le_of_lt (ZMod.val_lt (pick i h)))
  · intro i h x hx hAx
    obtain ⟨hy, hAy⟩ := hpick i h ⟨x, hx, hAx⟩
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    have hd := good_circle_observations_control_representatives h x (pick i h) hρ hx hy
      (hcircle i x (pick i h) hAx hAy)
    rw [← sub_div, abs_div, abs_of_pos hN] at hd
    simpa only [mul_comm ρ (N : ℝ)] using (div_le_iff₀ hN).mp hd

end Erdos3

end

end OAI
