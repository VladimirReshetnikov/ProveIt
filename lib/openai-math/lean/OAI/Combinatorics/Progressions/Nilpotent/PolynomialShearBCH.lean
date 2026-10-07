import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearFactorialIntegrality
import OAI.Combinatorics.Progressions.Polynomial.WeightedPolynomialEndomorphisms

namespace OAI

section

namespace Erdos3

open MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ : Type*}

noncomputable def polynomialShearAssociativeAction (w : σ → ℕ) (s : ℕ) :
    PolynomialShearLieAlgebra w ℚ →ₗ⁅ℚ⁆ weightedPolynomialEndAlgebra (R := ℚ) w s where
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

theorem polynomialShearAssociativeAction_positive (w : σ → ℕ) (s : ℕ)
    (D : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearAssociativeAction w s D ∈ (weightedPolynomialEndFiltration w s).layer 1 :=
  polynomialShearEnd_mem_drop w s 1 D.property

theorem polynomialShearExpOn_lieBCH (w : σ → ℕ) (s : ℕ)
    (D E : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearExpOn (lieBCH s D E) s = polynomialShearExpOn D s * polynomialShearExpOn E s := by
  let F := weightedPolynomialEndFiltration w s
  let φ := polynomialShearAssociativeAction w s
  have hp (A : PolynomialShearLieAlgebra w ℚ) : φ A ∈ F.layer 1 :=
    polynomialShearAssociativeAction_positive w s A
  have hnil (A : PolynomialShearLieAlgebra w ℚ) : IsNilpotent (φ A) :=
    F.isNilpotent_of_mem le_rfl (hp A)
  have he : IsNilpotent.exp (φ (lieBCH s D E)) = IsNilpotent.exp (φ D) * IsNilpotent.exp (φ E) := by
    rw [map_lieBCH, F.lieBCH_eq (hp D) (hp E)]
    exact exp_nilpotentBCH (F.layerAlgebra 1) F.positive_nilpotent (hp D) (hp E)
  have hv := congrArg (weightedPolynomialEndAlgebra (R := ℚ) w s).val he
  rw [map_mul, IsNilpotent.map_exp (hnil (lieBCH s D E)),
    IsNilpotent.map_exp (hnil D), IsNilpotent.map_exp (hnil E)] at hv
  exact hv

theorem polynomialShearExpAut_lieBCH (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (D E : PolynomialShearLieAlgebra w ℚ) :
    polynomialShearExpAut (lieBCH s D E) = polynomialShearExpAut D * polynomialShearExpAut E := by
  apply WeightedLoweringAut.degreeActionHom_injective s hw
  apply LinearEquiv.toLinearMap_injective
  change ((polynomialShearExpAut (lieBCH s D E)).degreeAction s).toLinearMap =
    ((polynomialShearExpAut D).degreeAction s).toLinearMap *
      ((polynomialShearExpAut E).degreeAction s).toLinearMap
  rw [polynomialShearExp_degreeAction, polynomialShearExp_degreeAction,
    polynomialShearExp_degreeAction]
  exact polynomialShearExpOn_lieBCH w s D E

noncomputable def polynomialShearBCHEquiv (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).Group ≃* WeightedLoweringAut w ℚ where
  toFun A := polynomialShearExpAut A.coord
  invFun e := ⟨polynomialShearLog e⟩
  left_inv A := NilpotentLieBCHGroup.ext (polynomialShearLog_exp A.coord)
  right_inv := polynomialShearExp_log
  map_mul' A B := polynomialShearExpAut_lieBCH w s hw A.coord B.coord

theorem weightedLoweringAut_isNilpotent (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Group.IsNilpotent (WeightedLoweringAut w ℚ) := by
  let := (polynomialShearFiltration w s hw).isNilpotentGroup
  exact Group.nilpotent_of_mulEquiv (polynomialShearBCHEquiv w s hw)

theorem weightedLoweringAut_nilpotencyClass_le (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Group.nilpotencyClass (WeightedLoweringAut w ℚ) ≤ s := by
  let := (polynomialShearFiltration w s hw).isNilpotentGroup
  exact (Group.nilpotencyClass_le_of_surjective (polynomialShearBCHEquiv w s hw).toMonoidHom
    (polynomialShearBCHEquiv w s hw).surjective).trans
      (polynomialShear_group_nilpotencyClass_le w s hw)

end Erdos3

end

end OAI
