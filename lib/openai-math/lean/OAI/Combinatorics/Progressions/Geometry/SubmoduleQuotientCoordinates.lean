import OAI.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
  (b : Basis ι ℚ V) (U : Submodule ℚ V) (D : Matrix κ ι ℚ)
  (hker : LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap)
  (hsurj : Function.Surjective D.mulVec)

noncomputable def submoduleQuotientCoordinateEquiv : (V ⧸ U) ≃ₗ[ℚ] (κ → ℚ) :=
  (Submodule.Quotient.equiv U (U.map b.equivFun.toLinearMap) b.equivFun rfl).trans
    (rationalQuotientEquiv D _ hker hsurj)

omit [Fintype κ] in
theorem submoduleQuotientCoordinateEquiv_mk (x : V) :
    submoduleQuotientCoordinateEquiv b U D hker hsurj (U.mkQ x) = D *ᵥ b.equivFun x :=
  rationalQuotientEquiv_apply_mk D _ hker hsurj _

noncomputable def submoduleQuotientCoordinateBasis : Basis κ ℚ (V ⧸ U) :=
  Basis.ofEquivFun (submoduleQuotientCoordinateEquiv b U D hker hsurj)

theorem submoduleQuotientCoordinateBasis_matrix [DecidableEq ι] [DecidableEq κ] :
    LinearMap.toMatrix b (submoduleQuotientCoordinateBasis b U D hker hsurj) U.mkQ = D := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply, submoduleQuotientCoordinateBasis, Basis.ofEquivFun_repr_apply]
  change (submoduleQuotientCoordinateEquiv b U D hker hsurj (U.mkQ (b j))) i = _
  rw [submoduleQuotientCoordinateEquiv_mk]
  simp [Basis.equivFun_self, Matrix.mulVec, dotProduct]

theorem submoduleQuotientCoordinateEquiv_symm [DecidableEq κ]
    (S : Matrix ι κ ℚ) (hS : D * S = 1) (y : κ → ℚ) :
    (submoduleQuotientCoordinateEquiv b U D hker hsurj).symm y = U.mkQ (b.equivFun.symm (S *ᵥ y)) := by
  apply (submoduleQuotientCoordinateEquiv b U D hker hsurj).injective
  rw [LinearEquiv.apply_symm_apply, submoduleQuotientCoordinateEquiv_mk,
    LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

end Erdos3

end

end OAI
