import OAI.Combinatorics.Progressions.Lattices.LatticeGaussianHyperplane
import OAI.Combinatorics.Progressions.Lattices.LatticeGaussianTemperature
import OAI.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem monomial_smul_sub_mem_lattice (Λ : Submodule ℤ E) {x y : E}
    (hxy : x - y ∈ Λ) (n : ℤ) (k : ℕ) :
    (n : ℝ) ^ k • x - (n : ℝ) ^ k • y ∈ Λ := by
  rw [← smul_sub, ← Int.cast_pow, Int.cast_smul_eq_zsmul]
  exact Λ.smul_mem (n ^ k) hxy

theorem exists_schmidt_hyperplane_transfer (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (ξ : E) (hξ : ξ ≠ 0) (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    (α : E) {N k : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hsmall : (N : ℝ) ^ k *
      (CircleFourier.integerDistance ((inner ℝ ξ α : ℝ) : CircleFourier.Circle) / ‖ξ‖) ≤ ε) :
    ∃ β : (normalFunctional ξ).ker, ∀ n : ℤ, |n| ≤ (N : ℤ) →
      Real.exp (-4 * Real.pi) *
          latticeGaussianMass (latticeHyperplane Λ (normalFunctional ξ)) ((1 + ε) ^ 2)
            ((n : ℝ) ^ k • β) ≤
        latticeGaussianMass Λ 1 ((n : ℝ) ^ k • α) := by
  obtain ⟨γ, β, hγβ, herror⟩ := exists_corrected_hyperplane_representative Λ ξ hξ w hwΛ hw α
  have hclose : (N : ℝ) ^ k * ‖α - γ‖ ≤ ε := by
    rw [norm_sub_rev, herror]
    exact hsmall
  refine ⟨β, ?_⟩
  intro n hn
  have htransfer := latticeGaussianMass_hyperplane_translate_le Λ (normalFunctional ξ)
    (t := (1 + ε) ^ 2)
    (sq_pos_of_pos (by linarith)) ((n : ℝ) ^ k • γ) ((n : ℝ) ^ k • β)
    (monomial_smul_sub_mem_lattice Λ hγβ n k)
  exact (mul_le_mul_of_nonneg_left htransfer (Real.exp_pos _).le).trans
    (latticeGaussianMass_orbit_stability Λ α γ hε hεone hclose n hn)

theorem exists_schmidt_hyperplane_transfer_at_temperature (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (ξ : E) (hξ : ξ ≠ 0) (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    (α : E) {N k : ℕ} {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hsmall : Real.sqrt t * ((N : ℝ) ^ k *
      (CircleFourier.integerDistance ((inner ℝ ξ α : ℝ) : CircleFourier.Circle) / ‖ξ‖)) ≤ ε) :
    ∃ β : (normalFunctional ξ).ker, ∀ n : ℤ, |n| ≤ (N : ℤ) →
      Real.exp (-4 * Real.pi) *
          latticeGaussianMass (latticeHyperplane Λ (normalFunctional ξ)) (t * (1 + ε) ^ 2)
            ((n : ℝ) ^ k • β) ≤
        latticeGaussianMass Λ t ((n : ℝ) ^ k • α) := by
  obtain ⟨γ, β, hγβ, herror⟩ := exists_corrected_hyperplane_representative Λ ξ hξ w hwΛ hw α
  have hclose : Real.sqrt t * ((N : ℝ) ^ k * ‖α - γ‖) ≤ ε := by
    rw [norm_sub_rev, herror]
    exact hsmall
  refine ⟨β, ?_⟩
  intro n hn
  have htransfer := latticeGaussianMass_hyperplane_translate_le Λ (normalFunctional ξ)
    (t := t * (1 + ε) ^ 2)
    (mul_pos ht (sq_pos_of_pos (by linarith))) ((n : ℝ) ^ k • γ) ((n : ℝ) ^ k • β)
    (monomial_smul_sub_mem_lattice Λ hγβ n k)
  exact (mul_le_mul_of_nonneg_left htransfer (Real.exp_pos _).le).trans
    (latticeGaussianMass_temperature_orbit_stability Λ α γ ht hε hεone hclose n hn)

end Erdos3

end

end OAI
