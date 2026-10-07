import OAI.Combinatorics.Progressions.Estimates.GaussianPerturbation
import OAI.Combinatorics.Progressions.Lattices.LatticeHyperplaneBasis

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem latticeGaussianMass_stability (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (x y : E) {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hxy : ‖x - y‖ ≤ ε) :
    Real.exp (-4 * Real.pi) * latticeGaussianMass Λ ((1 + ε) ^ 2) y ≤
      latticeGaussianMass Λ 1 x := by
  unfold latticeGaussianMass
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    ((lattice_gaussian_summable Λ (sq_pos_of_pos (by linarith)) y).mul_left _)
    (lattice_gaussian_summable Λ (by norm_num) x)
  intro m
  have he : ‖(x - (m : E)) - (y - (m : E))‖ ≤ ε := by
    simpa only [sub_sub_sub_cancel_right] using hxy
  have h := gaussian_perturbation_lower (x - (m : E)) (y - (m : E)) hε hεone he
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + ε), mul_pow] at h
  convert h using 1 <;> congr 2 <;> ring

theorem latticeGaussianMass_orbit_stability (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (α β : E) {N k : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hεone : ε ≤ 1) (hclose : (N : ℝ) ^ k * ‖α - β‖ ≤ ε)
    (n : ℤ) (hn : |n| ≤ (N : ℤ)) :
    Real.exp (-4 * Real.pi) * latticeGaussianMass Λ ((1 + ε) ^ 2) ((n : ℝ) ^ k • β) ≤
      latticeGaussianMass Λ 1 ((n : ℝ) ^ k • α) := by
  apply latticeGaussianMass_stability Λ _ _ hε hεone
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_pow]
  have hnR : |(n : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hn
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hnR k) (norm_nonneg _)).trans hclose

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussian_perturbation_at_temperature (x y : E) {t ε : ℝ}
    (ht : 0 ≤ t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hxy : Real.sqrt t * ‖x - y‖ ≤ ε) :
    Real.exp (-4 * Real.pi) * Real.exp (-Real.pi * (t * (1 + ε) ^ 2) * ‖y‖ ^ 2) ≤
      Real.exp (-Real.pi * t * ‖x‖ ^ 2) := by
  have he : ‖Real.sqrt t • x - Real.sqrt t • y‖ ≤ ε := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
    exact hxy
  have h := gaussian_perturbation_lower (Real.sqrt t • x) (Real.sqrt t • y) hε hεone he
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t),
    abs_of_nonneg (show 0 ≤ 1 + ε by linarith), mul_pow, Real.sq_sqrt ht] at h
  rw [show -Real.pi * (t * (1 + ε) ^ 2) * ‖y‖ ^ 2 =
    -Real.pi * ((1 + ε) ^ 2 * (t * ‖y‖ ^ 2)) by ring,
    show -Real.pi * t * ‖x‖ ^ 2 = -Real.pi * (t * ‖x‖ ^ 2) by ring]
  exact h

variable [FiniteDimensional ℝ E]

theorem latticeGaussianMass_temperature_stability (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (x y : E) {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hxy : Real.sqrt t * ‖x - y‖ ≤ ε) :
    Real.exp (-4 * Real.pi) * latticeGaussianMass Λ (t * (1 + ε) ^ 2) y ≤
      latticeGaussianMass Λ t x := by
  unfold latticeGaussianMass
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    ((lattice_gaussian_summable Λ (mul_pos ht (sq_pos_of_pos (by linarith))) y).mul_left _)
    (lattice_gaussian_summable Λ ht x)
  intro m
  apply gaussian_perturbation_at_temperature _ _ ht.le hε hεone
  simpa only [sub_sub_sub_cancel_right] using hxy

theorem latticeGaussianMass_temperature_orbit_stability (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (α β : E) {N k : ℕ} {t ε : ℝ}
    (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hclose : Real.sqrt t * ((N : ℝ) ^ k * ‖α - β‖) ≤ ε)
    (n : ℤ) (hn : |n| ≤ (N : ℤ)) :
    Real.exp (-4 * Real.pi) * latticeGaussianMass Λ (t * (1 + ε) ^ 2) ((n : ℝ) ^ k • β) ≤
      latticeGaussianMass Λ t ((n : ℝ) ^ k • α) := by
  apply latticeGaussianMass_temperature_stability Λ _ _ ht hε hεone
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_pow]
  have hnR : |(n : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hn
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hnR k) (norm_nonneg _)) (Real.sqrt_nonneg t)).trans hclose

end Erdos3

end

end OAI
