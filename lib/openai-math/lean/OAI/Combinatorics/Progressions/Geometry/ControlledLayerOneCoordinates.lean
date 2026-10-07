import OAI.Combinatorics.Progressions.Estimates.ReindexedFastCoefficientSection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : Submodule ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
  (b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸
    F.realFirstCoefficientFastSubmodule w hw U))
  (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
  (hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = F.realFastCoefficientHorizontal w hw U x)

include hη

omit [Fintype ι] in
theorem layerOne_equiv_symm_coordinates (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    η.symm x = fun i => b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ
      (F.realFirstCoefficientHorizontalSection w x)) (Fin.castLE ha i) := by
  apply η.injective
  rw [LinearEquiv.apply_symm_apply, hη]
  exact (F.realFirstCoefficientHorizontal_section w x).symm

omit [Fintype ι] in
theorem layerOne_equiv_representative
    (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (x : Fin a → ℝ) :
    η x = F.realFirstCoefficientHorizontal w (R (extendInitialCoordinates x)) := by
  have h := hη (b.equivFun.symm (extendInitialCoordinates x))
  simp only [LinearEquiv.apply_symm_apply, extendInitialCoordinates_castLE] at h
  rw [← hR] at h
  exact h

theorem layerOne_equiv_grid (l m : ℕ)
    (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (hgrid : ∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF w m (R y))
    (x : Fin a → ℝ) (hx : x ∈ realDenominatorGrid l) :
    ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x) ∈ realDenominatorGrid m := by
  rw [F.layerOne_equiv_representative w hw U b ha η hη R hR x]
  exact F.realFirstCoefficientHorizontal_grid e ω hF w m _
    (hgrid _ (extendInitialCoordinates_grid l x hx))

theorem layerOne_equiv_symm_grid (l m : ℕ)
    (hgrid : ∀ x, F.FirstCoefficientGrid e ω hF w l x →
      b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) ∈ realDenominatorGrid m)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (hx : ((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    η.symm x ∈ realDenominatorGrid m := by
  rw [F.layerOne_equiv_symm_coordinates w hw U b ha η hη x]
  exact realDenominatorGrid_comp m _
    (hgrid _ (F.realHorizontalSection_grid e ω hF w l x hx)) (Fin.castLE ha)

theorem layerOne_equiv_norm (C : ℝ) (hC : 0 ≤ C)
    (R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w)
    (hR : ∀ y, (F.realFirstCoefficientFastSubmodule w hw U).mkQ (R y) = b.equivFun.symm y)
    (hbound : ∀ (y : Fin d → ℝ) (M : ℝ), 0 ≤ M → (∀ j, |y j| ≤ M) →
      F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) (C * M) (R y))
    (x : Fin a → ℝ) :
    ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun (η x)‖ ≤ C * ‖x‖ := by
  rw [F.layerOne_equiv_representative w hw U b ha η hη R hR x]
  apply F.realFirstCoefficientHorizontal_bound e ω hF w (fun _ => 1)
    (mul_nonneg hC (norm_nonneg _))
  apply hbound _ ‖x‖ (norm_nonneg x)
  intro j
  exact (norm_le_pi_norm (extendInitialCoordinates x : Fin d → ℝ) j).trans
    (norm_extendInitialCoordinates_le x)

theorem layerOne_equiv_symm_norm (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (x : F.RealFirstCoefficientModule w) (M : ℝ), 0 ≤ M →
      F.FirstCoefficientSlowBound e ω hF w (fun _ => 1) M x → ∀ j,
        |b.equivFun ((F.realFirstCoefficientFastSubmodule w hw U).mkQ x) j| ≤ C * M)
    (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    ‖η.symm x‖ ≤ C * ‖((F.layerOneBasis e ω hF).baseChange ℝ).equivFun x‖ := by
  rw [F.layerOne_equiv_symm_coordinates w hw U b ha η hη x]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg _))).mpr
  intro i
  exact hbound _ _ (norm_nonneg _) (F.realHorizontalSection_slow_bound e ω hF w
    (fun _ => 1) (by intro i; norm_num) x (norm_nonneg _) le_rfl) (Fin.castLE ha i)

end Erdos3.NilpotentLieFiltration

end

end OAI
