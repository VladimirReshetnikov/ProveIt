import OAI.Combinatorics.Progressions.Fourier.FourierLawTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def weightedIntegerGridCoefficient {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (w : X → ℂ)
    (M : ℕ) [NeZero M] (k : J → Fin M) : ℂ :=
  p.complexMean (fun x => w x*rectangularGridCharacter M k (Y x))

theorem weightedIntegerGrid_inversion {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (w : X → ℂ)
    (M : ℕ) [NeZero M] (z : J → ℤ) :
    (∑ k : J → Fin M, weightedIntegerGridCoefficient p Y w M k * star (rectangularGridCharacter M k z)) =
      (M : ℂ)^Fintype.card J * p.complexMean
        (fun x => if integerGridResidue M (Y x) = integerGridResidue M z then w x else 0) := by
  classical
  calc
    _ = ∑ x, (p.weight x : ℂ)*w x*
        (∑ k : J → Fin M, rectangularGridCharacter M k (Y x)*star (rectangularGridCharacter M k z)) := by
      simp only [weightedIntegerGridCoefficient, FiniteProbabilityWeights.complexMean, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [rectangularGridCharacter_orthogonality, FiniteProbabilityWeights.complexMean, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : integerGridResidue M (Y x) = integerGridResidue M z
      · simp only [hx, ite_true]
        ring
      · simp only [hx, ite_false, mul_zero]

theorem weightedIntegerGrid_image_inversion {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (w : X → ℂ)
    (M : ℕ) [NeZero M] (z : J → ℤ)
    (hclose : ∀ x, p.weight x ≠ 0 → ∀ j, |Y x j-z j| < (M : ℤ)) :
    (∑ k : J → Fin M, weightedIntegerGridCoefficient p Y w M k * star (rectangularGridCharacter M k z)) =
      (M : ℂ)^Fintype.card J * p.complexMean (fun x => if Y x = z then w x else 0) := by
  classical
  rw [weightedIntegerGrid_inversion]
  congr 1
  unfold FiniteProbabilityWeights.complexMean
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
  · simp only [integerGridResidue_eq_iff_of_close M (Y x) z (hclose x hx)]

theorem weightedIntegerGrid_image_on_centered_box {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (w : X → ℂ)
    (M : ℕ) [NeZero M] (center z : J → ℤ) {Q K : ℕ}
    (hM : M = (2*Q+1)*K) (hK : 0 < K)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, |(Y x j : ℝ)-center j| ≤ (Q : ℝ)*K)
    (hz : centeredFundamentalBox Q K center z) :
    (∑ k : J → Fin M, weightedIntegerGridCoefficient p Y w M k * star (rectangularGridCharacter M k z)) =
      (M : ℂ)^Fintype.card J * p.complexMean (fun x => if Y x = z then w x else 0) := by
  apply weightedIntegerGrid_image_inversion
  intro x hx j
  have hy := (centeredFundamentalBox_iff Q K center (Y x)).mp
    (centeredFundamentalBox_of_support center (Y x) hK le_rfl (hY x hx)) j
  have hz' := (centeredFundamentalBox_iff Q K center z).mp hz j
  rw [hM, abs_lt]
  constructor <;> omega

theorem weightedIntegerGridCoefficient_norm_le_one {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (w : X → ℂ)
    (hw : ∀ x, ‖w x‖ ≤ 1) (M : ℕ) [NeZero M] (k : J → Fin M) :
    ‖weightedIntegerGridCoefficient p Y w M k‖ ≤ 1 := by
  apply (p.norm_complexMean_le_mean_norm _).trans
  calc
    _ = p.mean (fun x => ‖w x‖) := by
      simp only [norm_mul, rectangularGridCharacter_norm, mul_one]
    _ ≤ p.mean (fun _ => 1) := p.mean_mono hw
    _ = 1 := p.mean_const 1

theorem weightedIntegerGridCoefficient_mass {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (w : X → ℂ)
    (hw : ∀ x, ‖w x‖ ≤ 1) (M : ℕ) [NeZero M] :
    (∑ k : J → Fin M, ‖weightedIntegerGridCoefficient p Y w M k‖) ≤ (M : ℝ)^Fintype.card J := by
  calc
    _ ≤ ∑ _k : J → Fin M, (1 : ℝ) := Finset.sum_le_sum (fun k _ =>
      weightedIntegerGridCoefficient_norm_le_one p Y w hw M k)
    _ = _ := by simp

end Erdos3

end

end OAI
