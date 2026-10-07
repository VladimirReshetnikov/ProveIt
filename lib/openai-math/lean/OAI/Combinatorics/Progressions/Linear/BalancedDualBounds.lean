import Mathlib

namespace OAI

section

namespace Erdos3

theorem exists_complex_unit_phase (z : ℂ) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ a * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, by simp, by simp⟩
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨star z / (‖z‖ : ℂ), ?_, ?_⟩
  · simp [hn]
  · calc
      _ = (star z * z) / (‖z‖ : ℂ) := by ring
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) / (‖z‖ : ℂ) := by
        rw [mul_comm (star z) z]
        change z * (starRingEnd ℂ) z / (‖z‖ : ℂ) = _
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = _ := by
        rw [Complex.ofReal_pow]
        field_simp

theorem norm_lt_of_re_lt_on_balanced {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f : E →ₗ[ℂ] ℂ) {S : Set E} (hS : Balanced ℂ S) {c : ℝ}
    (hf : ∀ x ∈ S, (f x).re < c) : ∀ x ∈ S, ‖f x‖ < c := by
  intro x hx
  obtain ⟨a, ha, hphase⟩ := exists_complex_unit_phase (f x)
  have h := hf (a • x) (hS.smul_mem ha.le hx)
  simpa only [map_smul, smul_eq_mul, hphase, Complex.ofReal_re] using h

theorem seminorm_dual_bound_of_ball {E : Type*} [AddCommGroup E] [Module ℂ E]
    (X : Seminorm ℂ E) (f : E →ₗ[ℂ] ℂ) {tau : ℝ} (htau : 0 < tau)
    (hball : ∀ v, X v ≤ tau → ‖f v‖ < 1) : ∀ v, tau * ‖f v‖ ≤ X v := by
  intro v
  by_contra h
  have hv : X v < tau * ‖f v‖ := lt_of_not_ge h
  have hnorm : 0 < ‖f v‖ := by nlinarith [apply_nonneg X v, norm_nonneg (f v)]
  let a : ℂ := (‖f v‖⁻¹ : ℝ)
  have ha : ‖a‖ = ‖f v‖⁻¹ := by
    simp [a]
  have hX : X (a • v) ≤ tau := by
    rw [map_smul_eq_mul, ha, inv_mul_eq_div]
    exact ((div_lt_iff₀ hnorm).mpr (by simpa only [mul_comm] using hv)).le
  have hbad := hball (a • v) hX
  have hbad' : (1 : ℝ) < 1 := by
    simpa only [map_smul, norm_smul, ha, inv_mul_cancel₀ hnorm.ne'] using hbad
  exact (lt_irrefl 1) hbad'

end Erdos3

end

end OAI
