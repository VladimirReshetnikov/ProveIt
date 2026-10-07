import OAI.Combinatorics.Progressions.Lattices.LatticeGaussianDilation

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianMean_zero_term (Λ : Submodule ℤ E) (t : ℝ) (j N : ℕ) (α : E) :
    normalizedLatticeGaussian Λ t 0 ≤
      (2 * (N : ℝ) + 1) * latticeGaussianMean Λ t (j + 1) α N := by
  have h := Finset.single_le_sum
    (f := fun n : ℤ => normalizedLatticeGaussian Λ t ((n : ℝ) ^ (j + 1) • α))
    (fun n _ => normalizedLatticeGaussian_nonneg Λ t _) (by simp : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ))
  simp only [Int.cast_zero, zero_pow (Nat.succ_ne_zero j), zero_smul] at h
  unfold latticeGaussianMean
  simp only [symmetricInterval_card, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [mul_div_cancel₀ _ (by positivity : 2 * (N : ℝ) + 1 ≠ 0)]
  exact h

end Erdos3

end

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_nonzero_index_of_gaussian_mean (Λ : Submodule ℤ E) (t : ℝ)
    (α : E) (j N : ℕ) {D B : ℝ} (hD : 0 < D) (hB : 0 ≤ B)
    (hmean : 1 ≤ D * latticeGaussianMean Λ t (j + 1) α N)
    (hlength : 2 * D * normalizedLatticeGaussian Λ t 0 < 2 * (N : ℝ) + 1)
    (hsmall : 2 * D * B < 1) :
    ∃ n : ℤ, n ≠ 0 ∧ |n| ≤ (N : ℤ) ∧ B < normalizedLatticeGaussian Λ t ((n : ℝ) ^ (j + 1) • α) := by
  classical
  by_contra! hnone
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let f := fun n : ℤ => normalizedLatticeGaussian Λ t ((n : ℝ) ^ (j + 1) • α)
  let A := normalizedLatticeGaussian Λ t 0
  have hpoint (n : ℤ) (hn : n ∈ s) : f n ≤ (if n = 0 then A else 0) + B := by
    by_cases hzero : n = 0
    · subst n
      simp only [f, Int.cast_zero, zero_pow (Nat.succ_ne_zero j), zero_smul, ite_true]
      dsimp [A]
      linarith
    · simp only [hzero, ite_false, zero_add]
      exact hnone n hzero (abs_le.mpr (Finset.mem_Icc.mp hn))
  have hsum := Finset.sum_le_sum hpoint
  have h0 : (0 : ℤ) ∈ s := by simp [s]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', h0, ite_true,
    Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : (s.card : ℝ) = 2 * (N : ℝ) + 1 := by
    simp only [s, symmetricInterval_card, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [hc] at hsum
  have hmean' : (2 * (N : ℝ) + 1) * latticeGaussianMean Λ t (j + 1) α N = ∑ n ∈ s, f n := by
    unfold latticeGaussianMean
    change (2 * (N : ℝ) + 1) * ((∑ n ∈ s, f n) / (s.card : ℝ)) = _
    rw [hc, mul_div_cancel₀ _ (by positivity : 2 * (N : ℝ) + 1 ≠ 0)]
  have hlower := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 2 * (N : ℝ) + 1 by positivity)
  have hupper := mul_le_mul_of_nonneg_left hsum hD.le
  have htail := mul_lt_mul_of_pos_right hsmall (show 0 < 2 * (N : ℝ) + 1 by positivity)
  dsimp [A] at hupper
  nlinarith [hmean']

end Erdos3

end

end OAI
