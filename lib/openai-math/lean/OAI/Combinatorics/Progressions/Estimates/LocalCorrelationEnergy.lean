import OAI.Combinatorics.Progressions.Sampling.LocalWeightedSampling

namespace OAI

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem correlation_self_le_zero (L : Finset G) (f : G → ℝ) (t : G) :
    correlation L f f t ≤ correlation L f f 0 := by
  have hshift : (∑ x, f (x + t) ^ 2) = ∑ x, f x ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)
  have hsum : (∑ x, f (x + t) * f x) ≤ ∑ x, f x ^ 2 := by
    have h : (∑ x, 2 * (f (x + t) * f x)) ≤ ∑ x, (f (x + t) ^ 2 + f x ^ 2) :=
      Finset.sum_le_sum (fun x _ => by nlinarith [sq_nonneg (f (x + t) - f x)])
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hshift] at h
    linarith
  have h := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg L.card : (0 : ℝ) ≤ L.card)
  simpa only [correlation, add_zero, pow_two] using h

theorem correlation_average (L C : Finset G) (f : G → ℝ) (t : G) :
    correlation L (fun x => 𝔼 c ∈ C, f (x + c)) (fun x => 𝔼 c ∈ C, f (x + c)) t =
      𝔼 c ∈ C, 𝔼 d ∈ C, correlation L f f (t + c - d) := by
  change ((∑ x, (𝔼 c ∈ C, f ((x + t) + c)) * (𝔼 d ∈ C, f (x + d))) / L.card) = _
  simp_rw [Finset.expect_mul_expect, ← Finset.expect_sum_comm, Finset.expect_div]
  apply Finset.expect_congr rfl
  intro c _
  apply Finset.expect_congr rfl
  intro d _
  rw [correlation_eq_sum_add]
  simp only [add_assoc]

theorem opposite_average_correlation_le_square_mean (L C : Finset G) (f : G → ℝ) (t : G) :
    (𝔼 c ∈ C, 𝔼 d ∈ C, correlation L f f (t + c - d)) ≤
      (∑ x, (𝔼 c ∈ C, f (x + c)) ^ 2) / L.card := by
  rw [← correlation_average]
  have h := correlation_self_le_zero L (fun x => 𝔼 c ∈ C, f (x + c)) t
  simpa only [correlation, add_zero, pow_two] using h

end Erdos3.LocalConvolution

end

end OAI
