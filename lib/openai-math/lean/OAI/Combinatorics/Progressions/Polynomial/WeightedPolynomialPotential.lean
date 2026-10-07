import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

noncomputable def weightedPolynomialPotential (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  (d : ℚ)⁻¹ • ∑ i, w i • (X i * P i)

theorem weightedPolynomialPotential_pderiv_formula (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ) (i : σ) :
    pderiv i (weightedPolynomialPotential w d P) =
      (d : ℚ)⁻¹ • (w i • P i + ∑ j, w j • (X j * pderiv i (P j))) := by
  classical
  have hterm (j : σ) : pderiv i (w j • (X j * P j)) =
      (if j = i then w i • P i else 0) + w j • (X j * pderiv i (P j)) := by
    by_cases hji : j = i
    · subst j
      simp
      ring
    · simp [pderiv_X_of_ne hji, hji]
  rw [weightedPolynomialPotential, (pderiv i).map_smul, map_sum]
  simp only [hterm, Finset.sum_add_distrib]
  simp

theorem weightedPolynomialPotential_pderiv (w : σ → ℕ) {d : ℕ} (hd : 0 < d)
    (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (hclosed : ∀ i j, pderiv i (P j) = pderiv j (P i)) (i : σ) :
    pderiv i (weightedPolynomialPotential w d P) = P i := by
  rw [weightedPolynomialPotential_pderiv_formula]
  simp only [hclosed i]
  rw [(hhom i).sum_weight_X_mul_pderiv, ← add_nsmul, Nat.add_sub_of_le (hweight i)]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hd.ne'), one_smul]

theorem weightedPolynomialPotential_homogeneous (w : σ → ℕ) (d : ℕ)
    (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i)) :
    (weightedPolynomialPotential w d P).IsWeightedHomogeneous w d := by
  change weightedPolynomialPotential w d P ∈ weightedHomogeneousSubmodule ℚ w d
  apply (weightedHomogeneousSubmodule ℚ w d).smul_mem
  apply (weightedHomogeneousSubmodule ℚ w d).sum_mem
  intro i _
  have hprod : (X i * P i).IsWeightedHomogeneous w d := by
    have h := (isWeightedHomogeneous_X (R := ℚ) w i).mul (hhom i)
    simpa only [Nat.add_sub_of_le (hweight i)] using h
  exact (weightedHomogeneousSubmodule ℚ w d).nsmul_mem hprod (w i)

theorem exists_weighted_polynomial_primitive (w : σ → ℕ) {d : ℕ} (hd : 0 < d)
    (P : σ → MvPolynomial σ ℚ)
    (hweight : ∀ i, w i ≤ d)
    (hhom : ∀ i, (P i).IsWeightedHomogeneous w (d - w i))
    (hclosed : ∀ i j, pderiv i (P j) = pderiv j (P i)) :
    ∃ V : MvPolynomial σ ℚ, V.IsWeightedHomogeneous w d ∧
      ∀ i, pderiv i V = P i :=
  ⟨weightedPolynomialPotential w d P, weightedPolynomialPotential_homogeneous w d P hweight hhom,
    weightedPolynomialPotential_pderiv w hd P hweight hhom hclosed⟩

end Erdos3

end

end OAI
