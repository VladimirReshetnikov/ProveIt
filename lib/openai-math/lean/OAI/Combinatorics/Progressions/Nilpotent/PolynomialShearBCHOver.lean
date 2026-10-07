import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearRationalFiltration

namespace OAI

section

namespace Erdos3

open MvPolynomial
attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ R : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def polynomialShearAssociativeActionOver (w : σ → ℕ) (s : ℕ) :
    PolynomialShearLieAlgebra w R →ₗ⁅R⁆ weightedPolynomialEndAlgebra (R := R) w s where
  toLinearMap :=
    { toFun := fun D => ⟨polynomialShearEnd D s,
        weightedPolynomialEndDrop_antitone w s (Nat.zero_le 1)
          (polynomialShearEnd_mem_drop w s 1 D.property)⟩
      map_add' := by
        intro D E
        apply Subtype.ext
        exact (polynomialShearAction w s).map_add D E
      map_smul' := by
        intro c D
        apply Subtype.ext
        exact (polynomialShearAction w s).map_smul c D }
  map_lie' := by
    intro D E
    apply Subtype.ext
    exact (polynomialShearAction w s).map_lie D E

noncomputable def polynomialShearAssociativeRatAction (w : σ → ℕ) (s : ℕ) :
    PolynomialShearLieAlgebra w R →ₗ⁅ℚ⁆ weightedPolynomialEndAlgebra (R := R) w s where
  toLinearMap := (polynomialShearAssociativeActionOver (R := R) w s).toLinearMap.restrictScalars ℚ
  map_lie' := by
    intro D E
    exact (polynomialShearAssociativeActionOver (R := R) w s).map_lie D E

theorem polynomialShearAssociativeActionOver_positive (w : σ → ℕ) (s : ℕ)
    (D : PolynomialShearLieAlgebra w R) :
    polynomialShearAssociativeRatAction (R := R) w s D ∈ (weightedPolynomialEndRatFiltration (R := R) w s).layer 1 :=
  polynomialShearEnd_mem_drop w s 1 D.property

theorem polynomialShearExpOn_lieBCH_over (w : σ → ℕ) (s : ℕ)
    (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearExpOn (lieBCH s D E) s = polynomialShearExpOn D s * polynomialShearExpOn E s := by
  let F := weightedPolynomialEndRatFiltration (R := R) w s
  let φ := polynomialShearAssociativeRatAction (R := R) w s
  have hp (A : PolynomialShearLieAlgebra w R) : φ A ∈ F.layer 1 :=
    polynomialShearAssociativeActionOver_positive w s A
  have hnil (A : PolynomialShearLieAlgebra w R) : IsNilpotent (φ A) :=
    F.isNilpotent_of_mem le_rfl (hp A)
  have he : IsNilpotent.exp (φ (lieBCH s D E)) = IsNilpotent.exp (φ D) * IsNilpotent.exp (φ E) := by
    rw [map_lieBCH, F.lieBCH_eq (hp D) (hp E)]
    exact exp_nilpotentBCH (F.layerAlgebra 1) F.positive_nilpotent (hp D) (hp E)
  have hv := congrArg (weightedPolynomialEndAlgebra (R := R) w s).val he
  rw [map_mul, IsNilpotent.map_exp (hnil (lieBCH s D E)),
    IsNilpotent.map_exp (hnil D), IsNilpotent.map_exp (hnil E)] at hv
  exact hv

theorem polynomialShearExpAut_lieBCH_over (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (D E : PolynomialShearLieAlgebra w R) :
    polynomialShearExpAut (lieBCH s D E) = polynomialShearExpAut D * polynomialShearExpAut E := by
  apply WeightedLoweringAut.degreeActionHom_injective s hw
  apply LinearEquiv.toLinearMap_injective
  change ((polynomialShearExpAut (lieBCH s D E)).degreeAction s).toLinearMap =
    ((polynomialShearExpAut D).degreeAction s).toLinearMap *
      ((polynomialShearExpAut E).degreeAction s).toLinearMap
  rw [polynomialShearExp_degreeAction, polynomialShearExp_degreeAction,
    polynomialShearExp_degreeAction]
  exact polynomialShearExpOn_lieBCH_over w s D E

noncomputable def polynomialShearBCHEquivOver (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearRatFiltration (R := R) w s hw).Group ≃* WeightedLoweringAut w R where
  toFun A := polynomialShearExpAut A.coord
  invFun e := ⟨polynomialShearLog e⟩
  left_inv A := NilpotentLieBCHGroup.ext (polynomialShearLog_exp A.coord)
  right_inv := polynomialShearExp_log
  map_mul' A B := polynomialShearExpAut_lieBCH_over w s hw A.coord B.coord

end Erdos3

end

end OAI
