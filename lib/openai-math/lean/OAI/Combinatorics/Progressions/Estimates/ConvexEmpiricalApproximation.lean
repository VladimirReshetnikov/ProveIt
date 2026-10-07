import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_le_linear_of_mem_convexHull
    {E : Type*} [AddCommMonoid E] [Module ℝ E] {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) (f : E →ₗ[ℝ] ℝ) :
    ∃ q ∈ S, f q ≤ f z := by
  by_contra h
  push Not at h
  have hz' := (convexHull_min h (convex_halfSpace_gt f.isLinear (f z))) hz
  exact (lt_irrefl (f z)) hz'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem empirical_step_sq_le (u z q : E) {R : ℝ}
    (hchoice : inner ℝ (u - z) q ≤ inner ℝ (u - z) z) (hq : ‖q‖ ≤ R) :
    ‖u + (q - z)‖ ^ 2 ≤ ‖u‖ ^ 2 + R ^ 2 := by
  have hqsq := pow_le_pow_left₀ (norm_nonneg q) hq 2
  simp only [inner_sub_left, real_inner_self_eq_norm_sq] at hchoice
  rw [← real_inner_comm z q] at hchoice
  rw [norm_add_sq_real, norm_sub_sq_real, inner_sub_right]
  nlinarith only [hchoice, hqsq, sq_nonneg ‖z‖]

theorem exists_convex_empirical_sum {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) {R : ℝ} (hS : ∀ q ∈ S, ‖q‖ ≤ R) (n : ℕ) :
    ∃ q : Fin n → E, (∀ i, q i ∈ S) ∧
      ‖(∑ i, q i) - (n : ℝ) • z‖ ^ 2 ≤ (n : ℝ) * R ^ 2 := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, hsum⟩ := ih
    let u := (∑ i, q i) - (n : ℝ) • z
    obtain ⟨x, hx, hchoice⟩ := exists_le_linear_of_mem_convexHull hz
      (innerSL ℝ (u - z)).toLinearMap
    refine ⟨Fin.cons x q, ?_, ?_⟩
    · exact Fin.forall_fin_succ.mpr ⟨hx, hq⟩
    · have hid : (∑ i : Fin (n + 1), Fin.cons x q i) - ((n + 1 : ℕ) : ℝ) • z =
          u + (x - z) := by
        simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Nat.cast_add,
          Nat.cast_one, add_smul, one_smul]
        dsimp only [u]
        abel
      rw [hid]
      have hstep := empirical_step_sq_le u z x hchoice (hS x hx)
      change ‖u‖ ^ 2 ≤ (n : ℝ) * R ^ 2 at hsum
      push_cast
      nlinarith only [hsum, hstep]

theorem exists_convex_empirical_average {S : Set E} {z : E}
    (hz : z ∈ convexHull ℝ S) {R : ℝ} (hS : ∀ q ∈ S, ‖q‖ ≤ R)
    (n : ℕ) (hn : 0 < n) :
    ∃ q : Fin n → E, (∀ i, q i ∈ S) ∧
      ‖(n : ℝ)⁻¹ • (∑ i, q i) - z‖ ^ 2 ≤ R ^ 2 / n := by
  obtain ⟨q, hq, hsum⟩ := exists_convex_empirical_sum hz hS n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨q, hq, ?_⟩
  have hid : (n : ℝ)⁻¹ • ((∑ i, q i) - (n : ℝ) • z) =
      (n : ℝ)⁻¹ • (∑ i, q i) - z := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hnR.ne', one_smul]
  rw [← hid, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hnR.le), mul_pow]
  apply (mul_le_mul_of_nonneg_left hsum (sq_nonneg ((n : ℝ)⁻¹))).trans_eq
  field_simp

end Erdos3

end

end OAI
