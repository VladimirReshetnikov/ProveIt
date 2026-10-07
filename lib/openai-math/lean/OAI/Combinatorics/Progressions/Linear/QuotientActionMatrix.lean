import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {K V W ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem quotient_basis_representative (e : Basis ι K V) (f : Basis κ K W)
    (q : V →ₗ[K] W) (D : Matrix κ ι K) (S : Matrix ι κ K)
    (hD : LinearMap.toMatrix e f q = D) (hDS : D * S = 1) (y : κ → K) :
    f.equivFun.symm y = q (e.equivFun.symm (S *ᵥ y)) := by
  apply f.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  change y = f.repr (q (e.equivFun.symm (S *ᵥ y)))
  rw [← LinearMap.toMatrix_mulVec_repr e f q, hD]
  change y = D *ᵥ e.equivFun (e.equivFun.symm (S *ᵥ y))
  rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hDS, Matrix.one_mulVec]

theorem quotient_action_matrix (e : Basis ι K V) (f : Basis κ K W)
    (q : V →ₗ[K] W) (A : V →ₗ[K] V) (B : W →ₗ[K] W)
    (hAB : ∀ x, q (A x) = B (q x)) (S : Matrix ι κ K)
    (hS : LinearMap.toMatrix e f q * S = 1) :
    LinearMap.toMatrix f f B = LinearMap.toMatrix e f q * LinearMap.toMatrix e e A * S := by
  let L := Matrix.toLin f e S
  have hqL : q.comp L = LinearMap.id := by
    apply (LinearMap.toMatrix f f).injective
    rw [LinearMap.toMatrix_comp f e f, LinearMap.toMatrix_id]
    change LinearMap.toMatrix e f q * LinearMap.toMatrix f e (Matrix.toLin f e S) = 1
    rw [LinearMap.toMatrix_toLin, hS]
  have he : B = q.comp (A.comp L) := by
    ext x
    change B x = q (A (L x))
    rw [hAB, show q (L x) = x from DFunLike.congr_fun hqL x]
  rw [he, LinearMap.toMatrix_comp f e f, LinearMap.toMatrix_comp f e e]
  change LinearMap.toMatrix e f q *
    (LinearMap.toMatrix e e A * LinearMap.toMatrix f e (Matrix.toLin f e S)) = _
  rw [LinearMap.toMatrix_toLin, Matrix.mul_assoc]

end Erdos3

end

end OAI
