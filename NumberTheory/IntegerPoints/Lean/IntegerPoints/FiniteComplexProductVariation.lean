import IntegerPoints.FiniteComplexAbel
import Mathlib.Tactic

/-!
# Finite variation bounds for products of complex sequences

This theory-independent companion to `FiniteComplexAbel` bounds the exact Abel
variation of `u i * v i` by the endpoint norms and the first differences of
the two factors.  It imposes no positivity, monotonicity, phase, or
normalization hypothesis on either complex sequence.
-/

open scoped BigOperators

namespace LeanProofs.IntegerPoints

namespace FiniteComplexAbel

/-- One product difference splits into one first difference from each factor.
The asymmetric choice of endpoint is the one naturally used in a forward
finite variation sum. -/
theorem norm_mul_sub_mul_le
    (u₀ u₁ v₀ v₁ : ℂ) :
    ‖u₀ * v₀ - u₁ * v₁‖ ≤
      ‖u₀ - u₁‖ * ‖v₀‖ + ‖u₁‖ * ‖v₀ - v₁‖ := by
  rw [show u₀ * v₀ - u₁ * v₁ =
      (u₀ - u₁) * v₀ + u₁ * (v₀ - v₁) by ring]
  calc
    ‖(u₀ - u₁) * v₀ + u₁ * (v₀ - v₁)‖ ≤
        ‖(u₀ - u₁) * v₀‖ + ‖u₁ * (v₀ - v₁)‖ := norm_add_le _ _
    _ = ‖u₀ - u₁‖ * ‖v₀‖ + ‖u₁‖ * ‖v₀ - v₁‖ := by
      rw [norm_mul, norm_mul]

/-- Exact endpoint-and-first-difference majorant for the Abel variation of a
product.  There are no boundedness hypotheses and hence no hidden constants. -/
theorem variation_mul_le (u v : ℕ → ℂ) (K : ℕ) :
    variation (fun i ↦ u i * v i) K ≤
      ‖u K‖ * ‖v K‖ +
        ∑ i ∈ Finset.range K,
          (‖u i - u (i + 1)‖ * ‖v i‖ +
            ‖u (i + 1)‖ * ‖v i - v (i + 1)‖) := by
  unfold variation
  rw [norm_mul]
  refine add_le_add le_rfl ?_
  refine Finset.sum_le_sum fun i _hi ↦ ?_
  exact norm_mul_sub_mul_le (u i) (u (i + 1)) (v i) (v (i + 1))

/-- If both factors have uniform endpoint bounds through `K`, the product
variation is controlled by those bounds times the two exact first-difference
sums.  Nonnegativity of `U` and `V` follows from the stated finite hypotheses
and is not added as a redundant premise. -/
theorem variation_mul_le_of_uniform_norm_bounds
    (u v : ℕ → ℂ) (K : ℕ) (U V : ℝ)
    (hu : ∀ i, i ≤ K → ‖u i‖ ≤ U)
    (hv : ∀ i, i ≤ K → ‖v i‖ ≤ V) :
    variation (fun i ↦ u i * v i) K ≤
      U * V +
        V * (∑ i ∈ Finset.range K, ‖u i - u (i + 1)‖) +
        U * (∑ i ∈ Finset.range K, ‖v i - v (i + 1)‖) := by
  have hU : 0 ≤ U := (norm_nonneg (u K)).trans (hu K le_rfl)
  calc
    variation (fun i ↦ u i * v i) K ≤
        ‖u K‖ * ‖v K‖ +
          ∑ i ∈ Finset.range K,
            (‖u i - u (i + 1)‖ * ‖v i‖ +
              ‖u (i + 1)‖ * ‖v i - v (i + 1)‖) :=
      variation_mul_le u v K
    _ ≤ U * V +
          ∑ i ∈ Finset.range K,
            (‖u i - u (i + 1)‖ * V +
              U * ‖v i - v (i + 1)‖) := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul (hu K le_rfl) (hv K le_rfl) (norm_nonneg (v K)) hU
      · refine Finset.sum_le_sum fun i hi ↦ ?_
        have hiLt : i < K := Finset.mem_range.mp hi
        have hiLe : i ≤ K := Nat.le_of_lt hiLt
        have hiSucc : i + 1 ≤ K := Nat.add_one_le_iff.mpr hiLt
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hv i hiLe)
            (norm_nonneg (u i - u (i + 1))))
          (mul_le_mul_of_nonneg_right (hu (i + 1) hiSucc)
            (norm_nonneg (v i - v (i + 1))))
    _ = U * V +
          V * (∑ i ∈ Finset.range K, ‖u i - u (i + 1)‖) +
          U * (∑ i ∈ Finset.range K, ‖v i - v (i + 1)‖) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      ring

/-- Caller-facing version with arbitrary aggregate bounds for the two finite
first-difference sums.  No sign assumptions on `DU` or `DV` are required:
their necessary nonnegativity is already forced by `hdu` and `hdv`. -/
theorem variation_mul_le_of_uniform_norm_and_difference_sum_bounds
    (u v : ℕ → ℂ) (K : ℕ) (U V DU DV : ℝ)
    (hu : ∀ i, i ≤ K → ‖u i‖ ≤ U)
    (hv : ∀ i, i ≤ K → ‖v i‖ ≤ V)
    (hdu : (∑ i ∈ Finset.range K, ‖u i - u (i + 1)‖) ≤ DU)
    (hdv : (∑ i ∈ Finset.range K, ‖v i - v (i + 1)‖) ≤ DV) :
    variation (fun i ↦ u i * v i) K ≤ U * V + V * DU + U * DV := by
  have hU : 0 ≤ U := (norm_nonneg (u K)).trans (hu K le_rfl)
  have hV : 0 ≤ V := (norm_nonneg (v K)).trans (hv K le_rfl)
  calc
    variation (fun i ↦ u i * v i) K ≤
        U * V +
          V * (∑ i ∈ Finset.range K, ‖u i - u (i + 1)‖) +
          U * (∑ i ∈ Finset.range K, ‖v i - v (i + 1)‖) :=
      variation_mul_le_of_uniform_norm_bounds u v K U V hu hv
    _ ≤ U * V + V * DU + U * DV := by
      exact add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hdu hV))
        (mul_le_mul_of_nonneg_left hdv hU)

end FiniteComplexAbel

end LeanProofs.IntegerPoints
