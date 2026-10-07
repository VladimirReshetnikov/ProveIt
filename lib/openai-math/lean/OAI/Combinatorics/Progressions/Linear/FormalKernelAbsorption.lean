import OAI.Combinatorics.Progressions.Estimates.FastHorizontalFactorization

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

namespace VectorPolynomial

theorem homogeneous_one_pderiv {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (P : VectorPolynomial σ ℚ L)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ 1 → coefficients P α = 0)
    (i : σ) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L P = monomial 0 (coefficients P (Finsupp.single i 1)) := by
  classical
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [coefficients_pderiv, coefficients_monomial]
  by_cases hα : α = 0
  · subst α
    simp only [Finsupp.zero_apply, Nat.cast_zero, zero_add, one_smul, Finsupp.single_eq_same]
  · have hp := NilpotentLieFiltration.positive_weight_of_ne_zero (fun _ : σ => 1) (by simp) hα
    have hweight : Finsupp.weight (fun _ : σ => (1 : ℕ)) (α + Finsupp.single i 1) ≠ 1 := by
      rw [map_add, Finsupp.weight_single]
      simp only [one_smul]
      omega
    rw [hP _ hweight, smul_zero, Finsupp.single_eq_of_ne hα]

end VectorPolynomial

namespace NilpotentLieBCHGroup

variable {σ K L : Type*} [AddCommGroup K] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem PolynomialDerivativeSystemMod.absorb (V : Submodule ℚ L)
    (P : PolynomialGroup σ hnil) (S R : K →+ VectorPolynomial σ ℚ L)
    (small rational : σ → VectorPolynomial σ ℚ L) (k a b : σ → K)
    (hSR : PolynomialLiftSystemMod V P S R)
    (hsystem : PolynomialDerivativeSystemMod V P small rational (fun i => S (k i))) :
    PolynomialDerivativeSystemMod V P
      (fun i => small i + S (a i)) (fun i => rational i + R (b i))
      (fun i => S (k i - a i - b i)) := by
  intro i
  have h := (coefficientSubmodule V).add_mem (hsystem i) (hSR (b i))
  change formalLogDerivative i P -
    ((small i + S (a i)) + dualAdjoint P (rational i + R (b i)) + S (k i - a i - b i)) ∈ _
  convert h using 1
  simp only [map_sub, dualAdjoint_add]
  abel

theorem formal_remove_and_absorb (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P A B : PolynomialGroup σ hnil) (hA : ∀ α, coefficients A.coord α ∈ U)
    (S R : K →+ VectorPolynomial σ ℚ L)
    (small rational : σ → VectorPolynomial σ ℚ L) (k a b : σ → K)
    (hSR : PolynomialLiftSystemMod V P S R)
    (hsystem : PolynomialDerivativeSystemMod V P small rational (fun i => S (k i))) :
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R
    PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹) S' R' ∧
      PolynomialDerivativeSystemMod V (A⁻¹ * P * B⁻¹)
        (fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + S' (a i))
        (fun i => dualAdjoint B (rational i) - formalLogDerivative i B + R' (b i))
        (fun i => S' (k i - a i - b i)) := by
  intro S' R'
  have hlifts : PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹) S' R' :=
    PolynomialLiftSystemMod.remove U V hUV P A B hA S R hSR
  have hderivative := PolynomialDerivativeSystemMod.remove U V hUV P A B hA
    small rational (fun i => S (k i)) hsystem
  exact ⟨hlifts, PolynomialDerivativeSystemMod.absorb V (A⁻¹ * P * B⁻¹) S' R'
    _ _ k a b hlifts hderivative⟩

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
