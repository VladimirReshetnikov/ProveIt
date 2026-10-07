import OAI.Combinatorics.Progressions.Estimates.ControlledDetectedTranslationBaseBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

private def lieHomSubalgebra {A B : Type*} [LieRing A] [LieAlgebra ℚ A]
    [LieRing B] [LieAlgebra ℚ B] (f : A →ₗ⁅ℚ⁆ B) (K : LieSubalgebra ℚ B)
    (hf : ∀ x, f x ∈ K) : A →ₗ⁅ℚ⁆ K where
  toLinearMap := f.toLinearMap.codRestrict K.toSubmodule hf
  map_lie' {x y} := Subtype.ext (f.map_lie x y)

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hb : BasisHomogeneousBrackets b ω) (w : σ → ℕ)

include hb in
theorem realSymbolRepresentative_homogeneous_lie (x y : F.RealPolynomialSymbol w) :
    F.realSymbolRepresentative b ω hF w ⁅x, y⁆ =
      ⁅F.realSymbolRepresentative b ω hF w x, F.realSymbolRepresentative b ω hF w y⁆ := by
  let ψ : (ℝ ⊗[ℚ] F.AssociatedGraded) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L) :=
    { toLinearMap :=
        (realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).toLinearMap.restrictScalars ℚ
      map_lie' {x y} := (realificationLieHom
        (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).map_lie x y }
  let Ψ := LieAlgebra.ExtendScalars.map (AlgHom.id ℚ (MvPolynomial σ ℚ)) ψ
  have hΨ (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
      Ψ p = VectorPolynomial.map ψ.toLinearMap p := rfl
  simp only [F.realSymbolRepresentative_eq_homogeneous_map b ω hF hb w,
    (F.realGradedSymbolPolynomial b ω hF w).map_lie]
  exact Ψ.map_lie _ _

noncomputable def realHomogeneousAssociatedGradedMapQ :
    (ℝ ⊗[ℚ] F.AssociatedGraded) →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L) where
  toLinearMap :=
    (realificationLieHom (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).toLinearMap.restrictScalars ℚ
  map_lie' {x y} := (realificationLieHom
    (F.homogeneousAssociatedGradedEquiv b ω hF hb).toLieHom).map_lie x y

noncomputable def realHomogeneousSymbolRepresentativeLie :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ (MvPolynomial σ ℚ))
    (F.realHomogeneousAssociatedGradedMapQ b ω hF hb)).comp
      (F.realGradedSymbolPolynomial b ω hF w)

@[simp] theorem realHomogeneousSymbolRepresentativeLie_apply (x : F.RealPolynomialSymbol w) :
    F.realHomogeneousSymbolRepresentativeLie b ω hF hb w x =
      F.realSymbolRepresentative b ω hF w x := by
  exact (F.realSymbolRepresentative_eq_homogeneous_map b ω hF hb w x).symm

noncomputable def realHomogeneousAdaptedSymbolRepresentativeLie :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ F.realification.adaptedLieSubalgebra w :=
  lieHomSubalgebra (F.realHomogeneousSymbolRepresentativeLie b ω hF hb w)
    (F.realification.adaptedLieSubalgebra w) (fun x => by
      rw [F.realHomogeneousSymbolRepresentativeLie_apply]
      exact (F.realification.mem_adaptedSubmodule w _).mpr
        (F.realSymbolRepresentative_adapted b ω hF w x))

noncomputable def realHomogeneousPolynomialSymbolLiftHom :
    F.RealPolynomialSymbolGroup w →* (F.realification.adaptedPolynomialFiltration w).Group :=
  NilpotentLieBCHGroup.map (F.realHomogeneousAdaptedSymbolRepresentativeLie b ω hF hb w)

@[simp] theorem realHomogeneousPolynomialSymbolLiftHom_apply (g : F.RealPolynomialSymbolGroup w) :
    F.realHomogeneousPolynomialSymbolLiftHom b ω hF hb w g =
      F.realPolynomialSymbolLift b ω hF w g := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact F.realHomogeneousSymbolRepresentativeLie_apply b ω hF hb w g.coord

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie

open NilpotentLieFiltration

variable {U B : Type*} [Fintype B]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)

noncomputable def translationPolynomialSymbolLiftHom :
    (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1) →*
      (weightedFiltration w d hwd).realification.PolynomialOrbit (fun _ : U => 1) :=
  ((weightedFiltration w d hwd).realification.polynomialOrbitCoordinates
    (fun _ : U => 1)).symm.toMonoidHom.comp
      ((weightedFiltration w d hwd).realHomogeneousPolynomialSymbolLiftHom
        (weightedBasis w d hw) (weightedBasisGrade w d)
        (weightedFiltration_layer_eq_span w d hw hwd)
        (weightedBasis_homogeneous_brackets w d hw) (fun _ : U => 1))

@[simp] theorem translationPolynomialSymbolLiftHom_apply
    (g : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    translationPolynomialSymbolLiftHom w d hw hwd g =
      translationPolynomialSymbolLift w d hw hwd g := by
  unfold translationPolynomialSymbolLiftHom translationPolynomialSymbolLift
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    realHomogeneousPolynomialSymbolLiftHom_apply]

@[simp] theorem translationPolynomialSymbolLift_one :
    translationPolynomialSymbolLift w d hw hwd
      (1 : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) = 1 := by
  simpa only [translationPolynomialSymbolLiftHom_apply] using
    (translationPolynomialSymbolLiftHom (U := U) w d hw hwd).map_one

@[simp] theorem translationPolynomialSymbolLift_mul
    (g h : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1)) :
    translationPolynomialSymbolLift w d hw hwd (g * h) =
      translationPolynomialSymbolLift w d hw hwd g * translationPolynomialSymbolLift w d hw hwd h := by
  simpa only [translationPolynomialSymbolLiftHom_apply] using
    (translationPolynomialSymbolLiftHom w d hw hwd).map_mul g h

theorem translationPolynomialSymbolLift_factorization
    (E P R X : (weightedFiltration w d hwd).RealPolynomialSymbolGroup (fun _ : U => 1))
    (h : E * P * R = X) :
    translationPolynomialSymbolLift w d hw hwd E *
      translationPolynomialSymbolLift w d hw hwd P *
        translationPolynomialSymbolLift w d hw hwd R =
          translationPolynomialSymbolLift w d hw hwd X := by
  rw [← translationPolynomialSymbolLift_mul, ← translationPolynomialSymbolLift_mul, h]

end Erdos3.PolynomialTranslationLie

end

end OAI
