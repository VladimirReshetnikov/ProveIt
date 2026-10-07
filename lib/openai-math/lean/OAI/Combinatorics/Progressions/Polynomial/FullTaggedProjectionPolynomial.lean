import OAI.Combinatorics.Progressions.Lattices.CertifiedFullChartAffineTerminal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {X J : Type*} [Fintype J]

theorem linearMap_pi_apply_eq_sum
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (x : J → ℝ) (i : J) :
    P x i = ∑ a : J, P (Pi.single a 1) i * x a := by
  have hsum : ∑ a : J, x a • Pi.single a (1 : ℝ) = x := by
    ext a
    simp [Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [← hsum, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem sum_projection_coordinate_eq
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x)
    (poly : VectorPolynomial X ℝ (J → ℝ))
    (hm : ∀ α, coefficients poly α ∈ U) (i : J) :
    (∑ a : J, P (Pi.single a 1) i •
      coordinate (LinearMap.proj a : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly) =
      coordinate (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly := by
  ext α
  simp only [coeff_sum, coeff_smul, coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    LinearMap.proj_apply, smul_eq_mul]
  rw [← linearMap_pi_apply_eq_sum, hP _ (hm α)]

theorem sum_projection_C_eq
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x) (c : J → ℝ) (hc : c ∈ U) (i : J) :
    (∑ a : J, P (Pi.single a 1) i • C (c a) : MvPolynomial X ℝ) = C (c i) := by
  simp only [smul_eq_C_mul, ← C_mul, ← map_sum]
  rw [← linearMap_pi_apply_eq_sum, hP _ hc]

theorem sum_projection_coordinate_sub_C_eq
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x)
    (poly : VectorPolynomial X ℝ (J → ℝ))
    (hm : ∀ α, coefficients poly α ∈ U)
    (c : J → ℝ) (hc : c ∈ U) (i : J) :
    (∑ a : J, P (Pi.single a 1) i •
      (coordinate (LinearMap.proj a : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly - C (c a))) =
      coordinate (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly - C (c i) := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [sum_projection_coordinate_eq P U hP poly hm i, sum_projection_C_eq P U hP c hc i]

theorem sum_projection_remainder_eq
    {K : Type*}
    (P : (J → ℝ) →ₗ[ℝ] (J → ℝ)) (U : Submodule ℝ (J → ℝ))
    (hP : ∀ x, x ∈ U → P x = x)
    (poly : VectorPolynomial X ℝ (J → ℝ))
    (hm : ∀ α, coefficients poly α ∈ U)
    (c : J → ℝ) (hc : c ∈ U)
    (spatial : X → MvPolynomial K ℝ) (tag error : J → MvPolynomial K ℝ)
    (heq : ∀ a, aeval spatial
      (coordinate (LinearMap.proj a : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly) - C (c a) =
        error a + tag a) (i : J) :
    (∑ a : J, P (Pi.single a 1) i • tag a) -
        aeval spatial
          (coordinate (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom poly - C (c i)) =
      -(∑ a : J, P (Pi.single a 1) i • error a) := by
  have hcenter := congrArg (aeval spatial)
    (sum_projection_coordinate_sub_C_eq P U hP poly hm c hc i)
  simp only [map_sum, map_smul, map_sub, aeval_C, MvPolynomial.algebraMap_eq] at hcenter
  simp_rw [heq, smul_add] at hcenter
  rw [Finset.sum_add_distrib] at hcenter
  rw [map_sub, aeval_C, MvPolynomial.algebraMap_eq, heq i, ← hcenter]
  abel

end Erdos3.VectorPolynomial

end

end OAI
