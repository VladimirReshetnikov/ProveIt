import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem basis_projection_injective_of_minor {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (P : E →ₗ[K] (ι → K)) (p : Fin k → ι)
    (hdet : (Matrix.of (fun i j => P (b j) (p i))).det ≠ 0) : Function.Injective P := by
  let B := Matrix.of (fun i j => P (b j) (p i))
  have hB : IsUnit B := B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  have hxP : P x = 0 := hx
  have hcoord : B *ᵥ (fun j => b.repr x j) = 0 := by
    funext i
    have hs := congrArg (fun y => P y (p i)) (b.sum_repr x)
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    change (∑ j, B i j * b.repr x j) = 0
    calc
      _ = P x (p i) := by simpa only [B, Matrix.of_apply, mul_comm] using hs
      _ = 0 := congrFun hxP (p i)
  have hz : (fun j => b.repr x j) = 0 := Matrix.mulVec_injective_of_isUnit hB
    (hcoord.trans (Matrix.mulVec_zero B).symm)
  apply b.repr.injective
  simp only [map_zero]
  exact Finsupp.ext (fun j => congrFun hz j)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem basis_coordinate_matrix_mulVec {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (f : E →ₗ[K] (ι → K)) (x : E) :
    Matrix.of (fun i j => f (b j) i) *ᵥ (fun j => b.repr x j) = f x := by
  funext i
  have hs := congrArg (fun y => f y i) (b.sum_repr x)
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm] using hs

theorem basis_image_reconstruct_from_minor {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (f : E →ₗ[K] (ι → K)) (p : Fin k → ι)
    (hp : (Matrix.of (fun i j => f (b j) (p i))).det ≠ 0) (x : E) :
    let F := Matrix.of (fun i j => f (b j) i)
    (F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j)) = f x := by
  let F := Matrix.of (fun i j => f (b j) i)
  have hF : F *ᵥ (fun j => b.repr x j) = f x := basis_coordinate_matrix_mulVec b f x
  have hsub : (F.submatrix p id) *ᵥ (fun j => b.repr x j) = fun j => f x (p j) := by
    funext i
    exact congrFun hF (p i)
  have hp' : (F.submatrix p id).det ≠ 0 := hp
  change (F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j)) = f x
  rw [← hsub, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul (F.submatrix p id) (isUnit_iff_ne_zero.mpr hp'), Matrix.mul_one]
  exact hF

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem basis_projection_coefficients {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (P : E →ₗ[K] (ι → K)) (p : Fin k → ι)
    (hp : (Matrix.of (fun i j => P (b j) (p i))).det ≠ 0) (x : E) :
    (Matrix.of (fun i j => P (b j) (p i)))⁻¹ *ᵥ (fun i => P x (p i)) =
      fun j => b.repr x j := by
  let H := Matrix.of (fun i j => P (b j) (p i))
  have he : H *ᵥ (fun j => b.repr x j) = fun i => P x (p i) := by
    funext i
    exact congrFun (basis_coordinate_matrix_mulVec b P x) (p i)
  change H⁻¹ *ᵥ (fun i => P x (p i)) = _
  rw [← he, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hp), Matrix.one_mulVec]

theorem basis_map_from_projection_minor {K E ι κ : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (P : E →ₗ[K] (ι → K))
    (g : E →ₗ[K] (κ → K)) (p : Fin k → ι)
    (hp : (Matrix.of (fun i j => P (b j) (p i))).det ≠ 0) (x : E) :
    g x = (Matrix.of (fun i j => g (b j) i)) *ᵥ
      ((Matrix.of (fun i j => P (b j) (p i)))⁻¹ *ᵥ (fun i => P x (p i))) := by
  rw [basis_projection_coefficients b P p hp x]
  exact (basis_coordinate_matrix_mulVec b g x).symm

theorem exists_bounded_range_section {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →ₗ[ℝ] F) (hP : Function.Injective P) (C : ℝ)
    (hbound : ∀ x, ‖x‖ ≤ C * ‖P x‖) :
    ∃ J : LinearMap.range P →ₗ[ℝ] E,
      (∀ x, P (J x) = x.val) ∧ (∀ x, ‖J x‖ ≤ C * ‖x‖) := by
  let e := LinearEquiv.ofInjective P hP
  have he (x : LinearMap.range P) : P (e.symm x) = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  refine ⟨e.symm.toLinearMap, he, ?_⟩
  intro x
  calc
    ‖e.symm x‖ ≤ C * ‖P (e.symm x)‖ := hbound _
    _ = C * ‖x‖ := by rw [he]; rfl

theorem exists_normalized_basis_vector {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (g : E →ₗ[K] (ι → K))
    (B : Matrix ι (Fin k) K) (hB : ∀ i j, B i j = g (b j) i)
    (N : Matrix (Fin k) (Fin k) K) (j : Fin k) :
    ∃ v : E, g v = (B * N).col j := by
  refine ⟨∑ t, N t j • b t, ?_⟩
  funext i
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ t, N t j * g (b t) i) = ∑ t, B i t * N t j
  apply Finset.sum_congr rfl
  intro t _
  rw [hB, mul_comm]

end Erdos3

end

end OAI
