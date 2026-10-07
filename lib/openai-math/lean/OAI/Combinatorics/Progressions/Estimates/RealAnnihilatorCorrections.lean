import OAI.Combinatorics.Progressions.Linear.RealFourAnnihilatorKernel

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype I] [Fintype J]

theorem mem_realified_coordinate_kernel_iff_eq_zero
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker ℓ).baseChange ℝ ↔ realifyCoordinateMap ℓ x = 0 := by
  rw [mem_realified_coordinate_kernel_iff]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

theorem exists_real_annihilator_correction
    (b : Basis I ℚ V) (ℓ : V →ₗ[ℚ] (J → ℚ)) {H l : ℕ} {p : ℝ}
    (hℓ : ∀ j i, RationalHeightLE (ℓ (b i) j) H) (hp : 0 ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (x E Q : ℝ ⊗[ℚ] V) (ε : ℝ),
        x - E - Q ∈ (LinearMap.ker ℓ).baseChange ℝ →
        ‖(b.baseChange ℝ).equivFun E‖ ≤ ε →
        (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l →
        ∃ q ∈ realDenominatorGrid m,
          ‖realifyCoordinateMap ℓ x - q‖ ≤ Real.exp ((p + 2) ^ 3) * ε := by
  let A := coordinateFunctionalMatrix b ℓ
  have hm := matrixDenominator_allowance_le_exp A l H hℓ hp hJ hI hH hlp
  rw [Nat.mul_comm l] at hm
  refine ⟨matrixDenominator A * l, Nat.mul_pos (matrixDenominator_pos A) hl, hm,
    ⟨matrixDenominator A, Nat.mul_comm _ _⟩, ?_⟩
  intro x E Q ε hker hE hQ
  refine ⟨realifyCoordinateMap ℓ Q, realifyCoordinateMap_grid b ℓ l Q hQ, ?_⟩
  have hz := (mem_realified_coordinate_kernel_iff_eq_zero ℓ _).mp hker
  rw [map_sub, map_sub] at hz
  have heq : realifyCoordinateMap ℓ x - realifyCoordinateMap ℓ Q =
      realifyCoordinateMap ℓ E := by
    calc
      _ = (realifyCoordinateMap ℓ x - realifyCoordinateMap ℓ E -
          realifyCoordinateMap ℓ Q) + realifyCoordinateMap ℓ E := by abel
      _ = _ := by rw [hz, zero_add]
  rw [heq]
  have hfac : ((Fintype.card I : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    calc
      _ ≤ ((Fintype.card I : ℝ) + 1) * (Real.exp ((p + 2) ^ 1) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hHp : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
          hH.trans (Real.exp_le_exp.mpr (by rw [pow_one]; linarith))
        linarith
      _ ≤ _ := matrix_weighted_factor_le_exp_power (Fintype.card I) hp hI 1 (by decide)
  exact (realifyCoordinateMap_norm_bound b ℓ hℓ E).trans
    ((mul_le_mul_of_nonneg_right hfac (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hE (Real.exp_nonneg _)))

end Erdos3

end

end OAI
