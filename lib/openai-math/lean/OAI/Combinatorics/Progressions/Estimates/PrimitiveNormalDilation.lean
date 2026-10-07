import OAI.Combinatorics.Progressions.Polynomial.SchmidtShortDualVector

namespace OAI

section

namespace Erdos3

theorem integerDistance_le_abs_sub_integer (x : ℝ) (p : ℤ) :
    CircleFourier.integerDistance (x : CircleFourier.Circle) ≤ |x - p| := by
  rw [CircleFourier.integerDistance_coe]
  exact round_le x p

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem primitiveNormal_dilation_identity (α ξ ζ : E) (m p : ℤ) (q j : ℕ)
    (hξ : ξ = (m : ℝ) • ζ) :
    inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) -
        (((q : ℤ) * m) ^ j * p : ℤ) =
      ((((q : ℤ) * m : ℤ) : ℝ) ^ j) * ((q : ℝ) * inner ℝ ξ α - p) := by
  rw [hξ, inner_smul_right, real_inner_smul_left, pow_succ]
  push_cast
  ring

theorem primitiveNormal_dilation_error (α ξ ζ : E) (m p : ℤ) (q j : ℕ)
    (hξ : ξ = (m : ℝ) • ζ) {η : ℝ}
    (happrox : |(q : ℝ) * inner ℝ ξ α - p| ≤ η) :
    CircleFourier.integerDistance
        ((inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) : ℝ) : CircleFourier.Circle) ≤
      |(((q : ℤ) * m : ℤ) : ℝ)| ^ j * η := by
  calc
    _ ≤ |inner ℝ ζ ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α) -
        (((q : ℤ) * m) ^ j * p : ℤ)| := integerDistance_le_abs_sub_integer _ _
    _ = |(((q : ℤ) * m : ℤ) : ℝ)| ^ j * |(q : ℝ) * inner ℝ ξ α - p| := by
      rw [primitiveNormal_dilation_identity α ξ ζ m p q j hξ, abs_mul, abs_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left happrox (pow_nonneg (abs_nonneg _) _)

variable [FiniteDimensional ℝ E]

theorem exists_primitive_dilated_hyperplane_transfer (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (α ξ ζ : E) (m p : ℤ) (q j H : ℕ) (hξ : ξ = (m : ℝ) • ζ) (hζ : ζ ≠ 0)
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ζ w = 1)
    {t ε η : ℝ} (ht : 0 < t) (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (happrox : |(q : ℝ) * inner ℝ ξ α - p| ≤ η)
    (hroom : Real.sqrt t * ((H : ℝ) ^ (j + 1) *
      (|(((q : ℤ) * m : ℤ) : ℝ)| ^ j * η / ‖ζ‖)) ≤ ε) :
    ∃ β : (normalFunctional ζ).ker, ∀ n : ℤ, |n| ≤ (H : ℤ) →
      Real.exp (-4 * Real.pi) *
          latticeGaussianMass (latticeHyperplane Λ (normalFunctional ζ)) (t * (1 + ε) ^ 2)
            ((n : ℝ) ^ (j + 1) • β) ≤
        latticeGaussianMass Λ t
          ((n : ℝ) ^ (j + 1) • ((((q : ℤ) * m : ℤ) : ℝ) ^ (j + 1) • α)) := by
  apply exists_schmidt_hyperplane_transfer_at_temperature Λ ζ hζ w hwΛ hw _ ht hε hεone
  apply le_trans _ hroom
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
  exact div_le_div_of_nonneg_right (primitiveNormal_dilation_error α ξ ζ m p q j hξ happrox)
    (norm_nonneg ζ)

end Erdos3

end

end OAI
