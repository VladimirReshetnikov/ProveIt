import OAI.Combinatorics.Progressions.Nilpotent.PolynomialShearBCH

namespace OAI

section

namespace Erdos3

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] (w : σ → ℕ)

noncomputable instance (priority := 100) polynomialShearRatLieAlgebra :
    LieAlgebra ℚ (PolynomialShearLieAlgebra w R) where
  lie_smul c D E := by
    rw [← IsScalarTower.algebraMap_smul R c E, lie_smul, IsScalarTower.algebraMap_smul]

noncomputable def polynomialShearRatFiltration (s : ℕ) (hw : ∀ i, w i ≤ s) :
    NilpotentLieFiltration (PolynomialShearLieAlgebra w R) s where
  layer i := (polynomialShearLayer (R := R) w i).restrictScalars ℚ
  antitone := polynomialShearLayer_antitone w
  one_eq_top := by rw [polynomialShearLayer_one]; rfl
  lie_mem := polynomialShearLayer_bracket w _ _
  terminal := by rw [polynomialShearLayer_terminal w s hw]; rfl

noncomputable def weightedPolynomialEndRatLayer (s k : ℕ) :
    Submodule ℚ (weightedPolynomialEndAlgebra (R := R) w s) :=
  ((weightedPolynomialEndDrop w s k).comap
    (weightedPolynomialEndAlgebra (R := R) w s).val.toLinearMap).restrictScalars ℚ

noncomputable def weightedPolynomialEndRatFiltration (s : ℕ) :
    NilpotentAlgebraFiltration (weightedPolynomialEndAlgebra (R := R) w s) s where
  layer := weightedPolynomialEndRatLayer w s
  antitone := by
    intro a b hab F hF
    exact weightedPolynomialEndDrop_antitone w s hab hF
  zero_eq_top := by
    apply top_unique
    intro F hF
    exact F.property
  mul_mem := by
    intro a b F G hF hG
    exact weightedPolynomialEndDrop_mul w s a b hF hG
  terminal := by
    apply bot_unique
    intro F hF
    change F = 0
    exact Subtype.ext (weightedPolynomialEndDrop_terminal w s hF)

end Erdos3

end

end OAI
