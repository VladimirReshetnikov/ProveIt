import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition

namespace OAI

section

namespace Erdos3

universe u

theorem PolynomialCoordinatePartitionBound.mono {h p p' : ℕ} {K K' : ℝ}
    (hpartition : PolynomialCoordinatePartitionBound.{u} h K p)
    (hK : K ≤ K') (hp : p ≤ p') : PolynomialCoordinatePartitionBound.{u} h K' p' := by
  intro ι _ P hP N H hH hscale hsize
  apply hpartition ι P hP N H hH
  · exact (mul_le_mul_of_nonneg_right hK (by positivity)).trans hscale
  · exact (Nat.pow_le_pow_right hH (Nat.mul_le_mul_right _ hp)).trans hsize

theorem exists_uniform_coordinate_partition_bound (s : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ h ≤ s, PolynomialCoordinatePartitionBound.{u} h K p := by
  induction s with
  | zero =>
    refine ⟨1, 1, le_rfl, by omega, ?_⟩
    intro h hh
    have heq : h = 0 := by omega
    subst h
    exact polynomialCoordinatePartitionBound_zero
  | succ s ih =>
    obtain ⟨K, p, hK, hp, hpart⟩ := ih
    obtain ⟨K', p', hK', hp', hpart'⟩ := exists_polynomial_coordinate_partition_bound.{u} (s + 1)
    refine ⟨max K K', p + p', hK.trans (le_max_left _ _), by omega, ?_⟩
    intro h hh
    by_cases hs : h ≤ s
    · exact (hpart h hs).mono (le_max_left _ _) (by omega)
    · have heq : h = s + 1 := by omega
      subst h
      exact hpart'.mono (le_max_right _ _) (by omega)

end Erdos3

end

end OAI
