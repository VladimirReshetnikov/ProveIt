import OAI.Combinatorics.Progressions.Estimates.ShiftedGradedCalculus

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_coordinate (f : L →ₗ[ℚ] ℝ) (h : σ → ℚ)
    (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    f (coefficients (directionalDerivative h p) α) =
      ∑ i, (h i : ℝ) * (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1)) := by
  rw [coefficients_directionalDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Rat.smul_def, mul_assoc]

theorem directionalDerivative_scaled_coordinate_bound
    (f : L →ₗ[ℚ] ℝ) (p : VectorPolynomial σ ℚ L)
    (d : ℕ) (hdegree : ∀ (β : σ →₀ ℕ) (i : σ), d < β i → f (coefficients p β) = 0)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ β, |f (coefficients p β)| ≤ M / monomialScale T β)
    (h : σ → ℚ) (hh : ∀ i, |(h i : ℝ)| ≤ T i) (α : σ →₀ ℕ) :
    |f (coefficients (directionalDerivative h p) α)| ≤
      (Fintype.card σ : ℝ) * d * M / monomialScale T α := by
  classical
  rw [directionalDerivative_coordinate]
  have hscale := monomialScale_pos T hT α
  have hterm (i : σ) :
      |(h i : ℝ) * (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1))| ≤
        d * M / monomialScale T α := by
    by_cases hd : d < α i + 1
    · rw [hdegree _ i (by simpa using hd), mul_zero, abs_zero]
      positivity
    · have hdi : α i + 1 ≤ d := Nat.le_of_not_gt hd
      have hdir : (α i + 1 : ℝ) ≤ d := by exact_mod_cast hdi
      have hiScale : monomialScale T (α + Finsupp.single i 1) = monomialScale T α * T i := by
        rw [monomialScale_add]
        congr 1
        simp [monomialScale]
      have hcoef := hp (α + Finsupp.single i 1)
      rw [hiScale] at hcoef
      calc
        _ = |(h i : ℝ)| * (α i + 1 : ℝ) * |f (coefficients p (α + Finsupp.single i 1))| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α i + 1)]
        _ ≤ (T i * d) * (M / (monomialScale T α * T i)) :=
          mul_le_mul (mul_le_mul (hh i) hdir (by positivity) (hT i).le) hcoef
            (abs_nonneg _) (mul_nonneg (hT i).le (Nat.cast_nonneg d))
        _ = d * M / monomialScale T α := by
          field_simp [ne_of_gt hscale, ne_of_gt (hT i)]
  calc
    _ ≤ ∑ i, |(h i : ℝ) * (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : σ, (d : ℝ) * M / monomialScale T α := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp [mul_assoc, mul_div_assoc]

theorem directionalDerivative_integral_coordinate
    (f : L →ₗ[ℚ] ℝ) (p : VectorPolynomial σ ℚ L) (l : ℕ)
    (hp : ∀ β, ∃ z : ℤ, (z : ℝ) = (l : ℝ) * f (coefficients p β))
    (h : σ → ℤ) (α : σ →₀ ℕ) :
    ∃ z : ℤ, (z : ℝ) = (l : ℝ) *
      f (coefficients (directionalDerivative (fun i => (h i : ℚ)) p) α) := by
  classical
  let z : σ → ℤ := fun i => Classical.choose (hp (α + Finsupp.single i 1))
  have hz (i : σ) : (z i : ℝ) = (l : ℝ) * f (coefficients p (α + Finsupp.single i 1)) :=
    Classical.choose_spec (hp (α + Finsupp.single i 1))
  refine ⟨∑ i, h i * (α i + 1 : ℤ) * z i, ?_⟩
  rw [directionalDerivative_coordinate, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, Rat.cast_intCast]
  apply Finset.sum_congr rfl
  intro i _
  rw [hz]
  ring

end Erdos3.VectorPolynomial

end

end OAI
