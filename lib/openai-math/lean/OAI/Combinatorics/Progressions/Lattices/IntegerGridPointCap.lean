/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.WeightedApproximationCaps
import OAI.Combinatorics.Progressions.Probability.WeightedModeratePointMass

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerPointDensity_norm_le_fourier_sum {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ)
    (K M : ℕ) [NeZero M] (z : J → ℤ) :
    ‖(((K : ℝ) ^ Fintype.card J * ((p.toPMF.map Y) z).toReal : ℝ) : ℂ)‖ ≤
      ((K : ℝ) / M) ^ Fintype.card J * ∑ k, ‖integerGridCoefficient p Y M k‖ := by
  have hmass : finiteImageMass p Y z ≤ integerGridMass p Y M z := by
    apply p.mean_mono
    intro x
    by_cases hx : Y x = z
    · simp only [hx, ite_true, le_refl]
    · simp only [ite_eq_right hx]
      split_ifs <;> norm_num
  rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) ENNReal.toReal_nonneg)]
  rw [← finiteImageMass_eq_toPMF]
  calc
    _ ≤ integerGridDensity p Y K M z :=
      mul_le_mul_of_nonneg_left hmass (pow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ ‖(integerGridDensity p Y K M z : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ _ := by
      rw [integerGridDensity_fourier, norm_mul, norm_pow, norm_div,
        Complex.norm_natCast, Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      simp only [norm_mul, norm_star, rectangularGridCharacter_norm, mul_one, le_refl]

theorem pmf_bind_point_norm_le {X Y : Type*} (p : PMF X) (q : X → PMF Y)
    (K C : ℝ) (z : Y)
    (hcap : ∀ x, ‖((K * (q x z).toReal : ℝ) : ℂ)‖ ≤ C) :
    ‖((K * ((p.bind q) z).toReal : ℝ) : ℂ)‖ ≤ C := by
  rw [← pmf_bind_scaled_complex_average]
  exact pmf_complex_average_norm_le p _ hcap

end Erdos3

end

end OAI
