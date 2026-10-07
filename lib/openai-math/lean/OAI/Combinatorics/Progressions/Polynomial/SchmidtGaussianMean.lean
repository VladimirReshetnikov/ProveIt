import OAI.Combinatorics.Progressions.Lattices.LatticeSheetHaar

namespace OAI

section

namespace Erdos3

theorem one_add_pow_le_exp_one {r : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hbudget : (r : ℝ) * ε ≤ 1) : (1 + ε) ^ r ≤ Real.exp 1 := by
  calc
    _ ≤ (Real.exp ε) ^ r := pow_le_pow_left₀ (by linarith)
      (by simpa only [add_comm] using Real.add_one_le_exp ε) _
    _ = Real.exp ((r : ℝ) * ε) := (Real.exp_nat_mul ε r).symm
    _ ≤ _ := Real.exp_le_exp.mpr hbudget

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def latticeGaussianMean (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), normalizedLatticeGaussian Λ t ((n : ℝ) ^ k • α)) /
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ)

theorem latticeGaussianMean_nonneg (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E) (N : ℕ) :
    0 ≤ latticeGaussianMean Λ t k α N := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun _ _ => normalizedLatticeGaussian_nonneg Λ t _

theorem latticeGaussianMean_of_finrank_zero (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hd : Module.finrank ℝ E = 0) (t : ℝ) (k : ℕ) (α : E) (N : ℕ) :
    latticeGaussianMean Λ t k α N = 1 := by
  have hne : (Finset.Icc (-(N : ℤ)) (N : ℤ)).Nonempty := ⟨0, by simp⟩
  have hc : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  simp only [latticeGaussianMean, normalizedLatticeGaussian_of_finrank_zero Λ hd,
    Finset.sum_const, nsmul_eq_mul, mul_one, div_self hc]

theorem latticeGaussianMean_transfer
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (Λ : Submodule ℤ E) (Γ : Submodule ℤ F) (t s c C : ℝ) (k : ℕ) (α : E) (β : F) (N : ℕ)
    (h : ∀ n : ℤ, |n| ≤ (N : ℤ) →
      c * normalizedLatticeGaussian Γ s ((n : ℝ) ^ k • β) ≤
        C * normalizedLatticeGaussian Λ t ((n : ℝ) ^ k • α)) :
    c * latticeGaussianMean Γ s k β N ≤ C * latticeGaussianMean Λ t k α N := by
  unfold latticeGaussianMean
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun n hn => h n (abs_le.mpr (Finset.mem_Icc.mp hn))

theorem exists_schmidt_gaussian_mean_transfer (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0) (hξdual : ξ ∈ euclideanDualLattice Λ)
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1)
    (α : E) {N k : ℕ} {t ε : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hbudget : (Module.finrank ℝ (normalFunctional ξ).ker : ℝ) * ε ≤ 1)
    (hsmall : Real.sqrt t * ((N : ℝ) ^ k *
      (CircleFourier.integerDistance ((inner ℝ ξ α : ℝ) : CircleFourier.Circle) / ‖ξ‖)) ≤ ε) :
    ∃ β : (normalFunctional ξ).ker,
      Real.exp (-4 * Real.pi) * Real.sqrt t *
          latticeGaussianMean (latticeHyperplane Λ (normalFunctional ξ))
            (t * (1 + ε) ^ 2) k β N ≤
        Real.exp 1 * ‖ξ‖ * latticeGaussianMean Λ t k α N ∧
      Real.sqrt t * normalizedLatticeGaussian (latticeHyperplane Λ (normalFunctional ξ))
          (t * (1 + ε) ^ 2) 0 ≤
        Real.exp 1 * ‖ξ‖ * normalizedLatticeGaussian Λ t 0 := by
  have hint := (mem_euclideanDualLattice Λ ξ).mp hξdual
  obtain ⟨β, hβ⟩ := exists_normalized_schmidt_hyperplane_transfer Λ ξ hξ hint w hwΛ hw
    α ht hε hεone hsmall
  have hfactor : ‖ξ‖ * (1 + ε) ^ Module.finrank ℝ (normalFunctional ξ).ker ≤
      Real.exp 1 * ‖ξ‖ := by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (one_add_pow_le_exp_one hε hbudget) (norm_nonneg ξ)
  refine ⟨β, ?_, ?_⟩
  · exact (latticeGaussianMean_transfer Λ _ _ _ _ _ k α β N hβ).trans
      (mul_le_mul_of_nonneg_right hfactor (latticeGaussianMean_nonneg Λ t k α N))
  · exact (normalizedLatticeGaussian_hyperplane_origin_le Λ ξ hξ hint w hwΛ hw ht hε).trans
      (mul_le_mul_of_nonneg_right hfactor (normalizedLatticeGaussian_nonneg Λ t 0))

end Erdos3

end

end OAI
