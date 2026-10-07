import Mathlib.LinearAlgebra.Matrix.ToLin
import OAI.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def transportedLieConstants (c : ι → ι → ι → ℚ)
    (P : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (i j k : κ) : ℚ :=
  ∑ abc : ι × (ι × ι), P k abc.1 * c abc.2.1 abc.2.2 abc.1 * S abc.2.1 i * S abc.2.2 j

omit [Fintype κ] in
theorem transportedLieConstants_height (c : ι → ι → ι → ℚ)
    (P : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) {Hc HP HS : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) Hc)
    (hP : ∀ i j, RationalHeightLE (P i j) HP)
    (hS : ∀ i j, RationalHeightLE (S i j) HS) (i j k : κ) :
    RationalHeightLE (transportedLieConstants c P S i j k)
      ((Fintype.card ι ^ 3 + 1) * (HP * Hc * HS * HS) ^ (Fintype.card ι ^ 3)) := by
  classical
  have h := rationalHeightLE_sum
    (fun abc : ι × (ι × ι) => P k abc.1 * c abc.2.1 abc.2.2 abc.1 * S abc.2.1 i * S abc.2.2 j)
    (fun abc => (((hP k abc.1).mul (hc abc.2.1 abc.2.2 abc.1)).mul (hS abc.2.1 i)).mul (hS abc.2.2 j))
  simpa only [transportedLieConstants, Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc] using h

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

omit [Fintype κ] in
theorem transportedLieConstants_formula (e : Basis ι ℚ L) (P : Matrix κ ι ℚ)
    (S : Matrix ι κ ℚ) (a b : L) (i j k : κ)
    (ha : ∀ u, e.repr a u = S u i) (hb : ∀ u, e.repr b u = S u j) :
    (P *ᵥ e.repr ⁅a, b⁆) k = transportedLieConstants (lieStructureConstants e) P S i j k := by
  classical
  simp only [Matrix.mulVec, dotProduct, transportedLieConstants, lie_coordinate_formula,
    ha, hb, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem basisMatrix_mulVec (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L)
    (x : κ → ℚ) :
    LinearMap.toMatrix b e φ *ᵥ x = e.equivFun (φ (b.equivFun.symm x)) := by
  have h := LinearMap.toMatrix_mulVec_repr b e φ (b.equivFun.symm x)
  simpa only [← b.equivFun_apply, LinearEquiv.apply_symm_apply, ← e.equivFun_apply] using h

omit [DecidableEq ι] in
theorem basisMatrix_injective (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L)
    (hφ : Function.Injective φ) : Function.Injective (LinearMap.toMatrix b e φ).mulVec := by
  intro x y hxy
  rw [basisMatrix_mulVec, basisMatrix_mulVec] at hxy
  exact b.equivFun.symm.injective (hφ (e.equivFun.injective hxy))

omit [DecidableEq ι] in
theorem basisMatrix_surjective (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L)
    (hφ : Function.Surjective φ) : Function.Surjective (LinearMap.toMatrix b e φ).mulVec := by
  intro y
  obtain ⟨x, hx⟩ := hφ (e.equivFun.symm y)
  refine ⟨b.equivFun x, ?_⟩
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply, hx, LinearEquiv.apply_symm_apply]

omit [DecidableEq ι] in

theorem lieStructureConstants_embedding (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (P : Matrix κ ι ℚ)
    (hP : P * LinearMap.toMatrix b e φ.toLinearMap = 1) (i j k : κ) :
    lieStructureConstants b i j k = transportedLieConstants (lieStructureConstants e)
      P (LinearMap.toMatrix b e φ.toLinearMap) i j k := by
  have hretract (x : M) : P *ᵥ e.repr (φ x) = b.repr x := by
    change P *ᵥ e.repr (φ.toLinearMap x) = b.repr x
    rw [← LinearMap.toMatrix_mulVec_repr b e φ.toLinearMap x, Matrix.mulVec_mulVec,
      hP, Matrix.one_mulVec]
  rw [lieStructureConstants, ← congrFun (hretract ⁅b i, b j⁆) k, LieHom.map_lie]
  apply transportedLieConstants_formula
  · intro u
    exact (LinearMap.toMatrix_apply b e φ.toLinearMap u i).symm
  · intro u
    exact (LinearMap.toMatrix_apply b e φ.toLinearMap u j).symm

theorem lieStructureConstants_section (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (σ : M →ₗ[ℚ] L) (hσ : ∀ x, φ (σ x) = x) (i j k : κ) :
    lieStructureConstants b i j k = transportedLieConstants (lieStructureConstants e)
      (LinearMap.toMatrix e b φ.toLinearMap) (LinearMap.toMatrix b e σ) i j k := by
  have hbracket : ⁅b i, b j⁆ = φ ⁅σ (b i), σ (b j)⁆ := by rw [LieHom.map_lie, hσ, hσ]
  rw [lieStructureConstants, hbracket]
  change (b.repr (φ.toLinearMap ⁅σ (b i), σ (b j)⁆)) k = _
  rw [← congrFun (LinearMap.toMatrix_mulVec_repr e b φ.toLinearMap ⁅σ (b i), σ (b j)⁆) k]
  apply transportedLieConstants_formula
  · intro u
    exact (LinearMap.toMatrix_apply b e σ u i).symm
  · intro u
    exact (LinearMap.toMatrix_apply b e σ u j).symm

theorem basisMatrix_section (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (S : Matrix ι κ ℚ)
    (hS : LinearMap.toMatrix e b φ * S = 1) (x : M) :
    φ (Matrix.toLin b e S x) = x := by
  apply b.equivFun.injective
  change (b.repr (φ (Matrix.toLin b e S x)) : κ → ℚ) = b.repr x
  rw [← LinearMap.toMatrix_mulVec_repr e b φ, Matrix.repr_toLin,
    Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

theorem lieStructureConstants_quotient_matrix (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (S : Matrix ι κ ℚ)
    (hS : LinearMap.toMatrix e b φ.toLinearMap * S = 1) (i j k : κ) :
    lieStructureConstants b i j k = transportedLieConstants (lieStructureConstants e)
      (LinearMap.toMatrix e b φ.toLinearMap) S i j k := by
  simpa only [LinearMap.toMatrix_toLin] using
    lieStructureConstants_section e b φ (Matrix.toLin b e S)
      (basisMatrix_section e b φ.toLinearMap S hS) i j k

end Erdos3

end

end OAI
