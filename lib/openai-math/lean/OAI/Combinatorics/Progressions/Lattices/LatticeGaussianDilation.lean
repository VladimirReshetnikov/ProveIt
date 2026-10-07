import OAI.Combinatorics.Progressions.Polynomial.SchmidtGaussianMean

namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem latticeGaussianMean_dilation (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E)
    (a : ℤ) (ha : a ≠ 0) (H N : ℕ) (hsize : |(a : ℝ)| * H ≤ N) :
    (2 * (H : ℝ) + 1) * latticeGaussianMean Λ t k ((a : ℝ) ^ k • α) H ≤
      (2 * (N : ℝ) + 1) * latticeGaussianMean Λ t k α N := by
  have h := symmetricInterval_sum_dilation
    (fun n => normalizedLatticeGaussian Λ t ((n : ℝ) ^ k • α))
    (fun n => normalizedLatticeGaussian_nonneg Λ t _) a ha H N hsize
  have hid (n : ℤ) : ((a * n : ℤ) : ℝ) ^ k • α =
      (n : ℝ) ^ k • ((a : ℝ) ^ k • α) := by
    rw [Int.cast_mul, mul_pow, smul_smul, mul_comm]
  simp only [hid] at h
  unfold latticeGaussianMean
  simp only [symmetricInterval_card, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [mul_div_cancel₀ _ (by positivity : 2 * (H : ℝ) + 1 ≠ 0),
    mul_div_cancel₀ _ (by positivity : 2 * (N : ℝ) + 1 ≠ 0)]
  exact h

theorem latticeGaussianMean_dilation_loss (Λ : Submodule ℤ E) (t : ℝ) (k : ℕ) (α : E)
    (a : ℤ) (ha : a ≠ 0) (H N : ℕ) {K : ℝ}
    (hsize : |(a : ℝ)| * H ≤ N) (hK : 1 ≤ K) (hlength : (N : ℝ) ≤ 2 * K * H) :
    latticeGaussianMean Λ t k ((a : ℝ) ^ k • α) H ≤
      2 * K * latticeGaussianMean Λ t k α N := by
  have h := latticeGaussianMean_dilation Λ t k α a ha H N hsize
  have hratio : 2 * (N : ℝ) + 1 ≤ 2 * K * (2 * H + 1) := by nlinarith
  have hnonneg := latticeGaussianMean_nonneg Λ t k α N
  have hh : 0 < 2 * (H : ℝ) + 1 := by positivity
  have hupper := mul_le_mul_of_nonneg_right hratio hnonneg
  nlinarith

end Erdos3

end

end OAI
