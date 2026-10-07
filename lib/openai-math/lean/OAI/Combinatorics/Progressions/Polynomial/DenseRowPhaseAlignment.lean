import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative
import OAI.Combinatorics.Progressions.Linear.BalancedDualBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_dense_row_phase_alignment {G X : Type*} [Fintype G] [Nonempty G]
    (Q : Finset G) (S : Finset X) (f : G → X → ℂ) {δ ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdense : δ * Fintype.card G ≤ (Q.card : ℝ))
    (hcorr : ∀ t ∈ Q, ρ ≤ ‖𝔼 x ∈ S, f t x‖) :
    ∃ w : G → ℂ, (∀ t, ‖w t‖ ≤ 1) ∧ (∀ t, t ∉ Q → w t = 0) ∧
      δ * ρ ≤ (𝔼 t, 𝔼 x ∈ S, w t * f t x).re := by
  classical
  choose c hc hphase using fun t => exists_complex_unit_phase (𝔼 x ∈ S, f t x)
  let w (t : G) := if t ∈ Q then c t else 0
  have hpoint (t : G) : (𝔼 x ∈ S, w t * f t x).re =
      if t ∈ Q then ‖𝔼 x ∈ S, f t x‖ else 0 := by
    rw [← Finset.mul_expect]
    by_cases ht : t ∈ Q
    · simp only [w, ht, ite_true, hphase, Complex.ofReal_re]
    · simp only [w, ht, ite_false, zero_mul, Complex.zero_re]
  have hsum : ρ * (Q.card : ℝ) ≤
      ∑ t : G, if t ∈ Q then ‖𝔼 x ∈ S, f t x‖ else 0 := by
    calc
      _ = ∑ t : G, if t ∈ Q then ρ else 0 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun t _ => by
        by_cases ht : t ∈ Q
        · simpa only [ht, ite_true] using hcorr t ht
        · simp only [ht, ite_false, le_refl]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Q <;> simp [w, ht, hc]
  · intro t ht
    simp only [w, ht, ite_false]
  · rw [expect_re]
    simp_rw [hpoint]
    rw [Fintype.expect_eq_sum_div_card]
    apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card G)).mpr
    calc
      _ = (δ * Fintype.card G) * ρ := by ring
      _ ≤ (Q.card : ℝ) * ρ := mul_le_mul_of_nonneg_right hdense hρ
      _ = ρ * (Q.card : ℝ) := mul_comm _ _
      _ ≤ _ := hsum

end Erdos3

end

end OAI
