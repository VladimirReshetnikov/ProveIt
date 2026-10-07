import OAI.Combinatorics.Progressions.Estimates.DependentPatchValue

namespace OAI

section

namespace Erdos3.TriangularSlots

open scoped BigOperators

variable {d : ℕ} (A : TriangularSlots d)

theorem tsum_eq_at_of_residual_bound (f : (Fin d → ℝ) → ℝ) {R : ℝ}
    (hgap : R + R < 1) (hsupport : ∀ x, f x ≠ 0 → ∀ i, |x i| ≤ R)
    (b : Fin d → ℤ) (hb : ∀ i, |A.residual b i| ≤ R) :
    (∑' z, f (A.residual z)) = f (A.residual b) := by
  apply tsum_eq_single b
  intro z hzb
  by_contra hz
  exact hzb (A.integer_unique hgap (hsupport _ hz) hb)

theorem tsum_approx_finite_family {I : Type*} [Fintype I]
    (f : (Fin d → ℝ) → ℝ) (g : I → (Fin d → ℝ) → ℝ) (c : I → ℝ)
    {R ε : ℝ} (hgap : R + R < 1) (hε : 0 ≤ ε)
    (hf : ∀ x, f x ≠ 0 → ∀ j, |x j| ≤ R)
    (hg : ∀ i x, g i x ≠ 0 → ∀ j, |x j| ≤ R)
    (happrox : ∀ x, |f x - ∑ i, c i * g i x| ≤ ε) :
    |(∑' z, f (A.residual z)) - ∑ i, c i * ∑' z, g i (A.residual z)| ≤ ε := by
  classical
  by_cases h : ∃ z : Fin d → ℤ, f (A.residual z) ≠ 0 ∨ ∃ i, g i (A.residual z) ≠ 0
  · obtain ⟨z, hz⟩ := h
    have hb : ∀ j, |A.residual z j| ≤ R := by
      rcases hz with hz | ⟨i, hi⟩
      · exact hf _ hz
      · exact hg i _ hi
    rw [A.tsum_eq_at_of_residual_bound f hgap hf z hb]
    simp_rw [A.tsum_eq_at_of_residual_bound _ hgap (hg _) z hb]
    exact happrox _
  · have hfzero (z : Fin d → ℤ) : f (A.residual z) = 0 := by
      by_contra hz
      exact h ⟨z, Or.inl hz⟩
    have hgzero (i : I) (z : Fin d → ℤ) : g i (A.residual z) = 0 := by
      by_contra hz
      exact h ⟨z, Or.inr ⟨i, hz⟩⟩
    simp only [hfzero, hgzero, tsum_zero, mul_zero, Finset.sum_const_zero, sub_self, abs_zero]
    exact hε

end Erdos3.TriangularSlots

end

end OAI
