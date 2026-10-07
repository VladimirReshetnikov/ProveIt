import OAI.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
import OAI.Combinatorics.Progressions.Geometry.SubmoduleQuotientCoordinates

namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix TensorProduct

theorem exists_submoduleQuotientSectionBasis_with_coordinates
    {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : Submodule ℚ V) (D : Matrix κ ι ℚ) (T : Matrix ι κ ℚ)
    (hker : LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap)
    (hDT : D * T = 1) :
    ∃ (eQ : Basis κ ℚ (V ⧸ U)) (S : (V ⧸ U) →ₗ[ℚ] V),
      Function.RightInverse S U.mkQ ∧
      Function.RightInverse (S.baseChange ℝ) (U.mkQ.baseChange ℝ) ∧
      (∀ i j, b.repr (S (eQ j)) i = T i j) ∧
      (∀ i j, (b.baseChange ℝ).repr (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i =
        (T i j : ℝ)) ∧
      ∀ j i, eQ.repr (U.mkQ (b i)) j = D j i := by
  have hsurj : Function.Surjective D.mulVec := by
    intro y
    refine ⟨T *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, hDT, Matrix.one_mulVec]
  let eQ := submoduleQuotientCoordinateBasis b U D hker hsurj
  let S : (V ⧸ U) →ₗ[ℚ] V := b.equivFun.symm.toLinearMap.comp
    (T.mulVecLin.comp eQ.equivFun.toLinearMap)
  have hright : Function.RightInverse S U.mkQ := by
    intro y
    change U.mkQ (b.equivFun.symm (T *ᵥ eQ.equivFun y)) = y
    rw [← submoduleQuotientCoordinateEquiv_symm b U D hker hsurj T hDT]
    exact (submoduleQuotientCoordinateEquiv b U D hker hsurj).symm_apply_apply y
  have hentry (i : ι) (j : κ) : b.repr (S (eQ j)) i = T i j := by
    change b.equivFun (b.equivFun.symm (T *ᵥ eQ.equivFun (eQ j))) i = T i j
    rw [LinearEquiv.apply_symm_apply]
    simp [Matrix.mulVec, dotProduct, Basis.equivFun_self]
  refine ⟨eQ, S, hright, ?_, hentry, ?_, ?_⟩
  · have heq : U.mkQ.comp S = LinearMap.id := LinearMap.ext hright
    have heqR := congrArg (fun f : (V ⧸ U) →ₗ[ℚ] (V ⧸ U) => f.baseChange ℝ) heq
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at heqR
    intro x
    exact DFunLike.congr_fun heqR x
  · intro i j
    rw [scalarExtension_basis_coordinates, hentry]
  · intro j i
    have hmatrix := submoduleQuotientCoordinateBasis_matrix b U D hker hsurj
    have h := congrFun (congrFun hmatrix j) i
    simpa only [LinearMap.toMatrix_apply] using h

theorem exists_submoduleQuotientSectionBasis
    {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (U : Submodule ℚ V) (D : Matrix κ ι ℚ) (T : Matrix ι κ ℚ)
    (hker : LinearMap.ker D.mulVecLin = U.map b.equivFun.toLinearMap)
    (hDT : D * T = 1) :
    ∃ (eQ : Basis κ ℚ (V ⧸ U)) (S : (V ⧸ U) →ₗ[ℚ] V),
      Function.RightInverse S U.mkQ ∧
      Function.RightInverse (S.baseChange ℝ) (U.mkQ.baseChange ℝ) ∧
      (∀ i j, b.repr (S (eQ j)) i = T i j) ∧
      ∀ i j, (b.baseChange ℝ).repr (S.baseChange ℝ ((eQ.baseChange ℝ) j)) i =
        (T i j : ℝ) := by
  obtain ⟨eQ, S, hright, hrightR, hentry, hentryR, _hcoord⟩ :=
    exists_submoduleQuotientSectionBasis_with_coordinates b U D T hker hDT
  exact ⟨eQ, S, hright, hrightR, hentry, hentryR⟩

end Erdos3

end

end OAI
