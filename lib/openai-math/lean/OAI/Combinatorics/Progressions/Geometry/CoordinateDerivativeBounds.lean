import OAI.Combinatorics.Progressions.Estimates.RealFirstCoefficientHorizontal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]

theorem directionalDerivative_single_coordinate (f : L →ₗ[ℚ] ℝ)
    (p : VectorPolynomial σ ℚ L) (i : σ) (α : σ →₀ ℕ) :
    f (coefficients (directionalDerivative (Pi.single i 1) p) α) =
      (α i + 1 : ℝ) * f (coefficients p (α + Finsupp.single i 1)) := by
  rw [directionalDerivative_coordinate]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem directionalDerivative_single_scaled_bound
    (f : L →ₗ[ℚ] ℝ) (p : VectorPolynomial σ ℚ L)
    (d : ℕ) (hdegree : ∀ (β : σ →₀ ℕ) (i : σ), d < β i → f (coefficients p β) = 0)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ β, |f (coefficients p β)| ≤ M / monomialScale T β) (i : σ) (α : σ →₀ ℕ) :
    |f (coefficients (directionalDerivative (Pi.single i 1) p) α)| ≤
      ((d : ℝ) * M / T i) / monomialScale T α := by
  rw [directionalDerivative_single_coordinate]
  by_cases hd : d < α i + 1
  · rw [hdegree _ i (by simpa using hd), mul_zero, abs_zero]
    exact div_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg d) hM) (hT i).le)
      (monomialScale_pos T hT α).le
  · have hdi : (α i + 1 : ℝ) ≤ d := by exact_mod_cast Nat.le_of_not_gt hd
    have hscale : monomialScale T (α + Finsupp.single i 1) = monomialScale T α * T i := by
      rw [monomialScale_add]
      simp [monomialScale]
    have hcoef := hp (α + Finsupp.single i 1)
    rw [hscale] at hcoef
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α i + 1)]
    calc
      _ ≤ (d : ℝ) * (M / (monomialScale T α * T i)) :=
        mul_le_mul hdi hcoef (abs_nonneg _) (Nat.cast_nonneg d)
      _ = _ := by ring

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem realAdaptedDirectionalDerivative_single_bound
    {σ ι L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra (fun _ : σ => 1))
    (hx : F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T M x) (i : σ) :
    F.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T ((s : ℝ) * M / T i)
      (F.realAdaptedDirectionalDerivative (Pi.single i 1) x) := by
  have hp := (F.realAdaptedCoefficientBound_polynomial_iff b ω hF (fun _ => 1) T hT hM
    (⟨x⟩ : F.RealAdaptedPolynomialGroup (fun _ => 1))).mp hx
  intro z
  rw [← F.realAdaptedPolynomialTensor_coordinates (fun _ => 1) b ω hF,
    F.realAdaptedDirectionalDerivative_polynomial]
  let f := ((b.baseChange ℝ).coord z.val.2).restrictScalars ℚ
  have hdegree : ∀ (β : σ →₀ ℕ) (j : σ), s < β j →
      f (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) x) β) = 0 := by
    intro β j hj
    have hβ := Finsupp.le_weight (fun _ : σ => 1) (s := j) (by decide) β
    have hi := F.adaptedBasis_weight_le_step b ω hF z.val.2
    have hni : ¬Finsupp.weight (fun _ : σ => 1) β ≤ ω z.val.2 := by omega
    exact (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mp
      ((F.realification.adapted_iff_coefficients (fun _ => 1) _).mp
        (F.realAdaptedPolynomialMap_adapted (fun _ => 1) x) β) z.val.2 hni
  exact directionalDerivative_single_scaled_bound f
    (F.realAdaptedPolynomialMap (fun _ => 1) x) s hdegree T hT M hM
    (fun β => hp β z.val.2) i z.val.1

end Erdos3.NilpotentLieFiltration

end

end OAI
