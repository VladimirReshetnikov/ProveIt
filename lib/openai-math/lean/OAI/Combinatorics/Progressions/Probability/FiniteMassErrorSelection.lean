import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_mass_error_point {X : Type*} [Fintype X] [Nonempty X]
    (A B : X → ℝ) {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε)
    (hA : ∀ x, A x ≤ 1) (hB : ∀ x, 0 ≤ B x)
    (hmass : m ≤ 𝔼 x, A x) (herr : (𝔼 x, B x) ≤ ε) :
    ∃ x, m / 2 ≤ A x ∧ B x ≤ 2 * ε / m := by
  let c := m / (2 * ε)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcancel : c * ε = m / 2 := by
    dsimp [c]
    field_simp
  have hscore : m / 2 ≤ (𝔼 x, (A x - c * B x)) := by
    rw [Finset.expect_sub_distrib, ← Finset.mul_expect]
    have hupper := mul_le_mul_of_nonneg_left herr hc.le
    rw [hcancel] at hupper
    linarith
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hscore
  refine ⟨x, ?_, ?_⟩
  · linarith [mul_nonneg hc.le (hB x)]
  · apply (mul_le_mul_iff_right₀ hc).mp
    calc
      c * B x ≤ 1 := by linarith [hA x]
      _ = c * (2 * ε / m) := by
        dsimp [c]
        field_simp

end Erdos3

end

end OAI
