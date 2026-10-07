import OAI.Combinatorics.Progressions.Estimates.EuclideanGraphResidual
import OAI.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds

namespace OAI

section

namespace Erdos3

noncomputable def euclideanVerticalMap {σ κ : Type*}
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) :
    (κ → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (σ ⊕ κ) :=
  productEuclideanEquiv.toLinearMap.comp ((LinearMap.inr ℝ (σ → ℝ) (κ → ℝ)).comp
    ((coordinateScaleEquiv scale hscale).toLinearMap.comp A.toLinearMap))

@[simp] theorem euclideanVerticalMap_apply_inl {σ κ : Type*}
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (x : κ → ℝ) (i : σ) :
    euclideanVerticalMap (σ := σ) scale hscale A x (Sum.inl i) = 0 := rfl

@[simp] theorem euclideanVerticalMap_apply_inr {σ κ : Type*}
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (x : κ → ℝ) (j : κ) :
    euclideanVerticalMap (σ := σ) scale hscale A x (Sum.inr j) = scale j * A x j := rfl

theorem euclideanDerivative_vertical_grid_coordinates
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (v : EuclideanSpace ℝ (σ ⊕ κ))
    (hv : v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl)
    (hzero : euclideanDerivativeShiftMap T hT v = 0) :
    ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧ v = euclideanVerticalMap scale hscale A r := by
  have hv' := (euclideanDerivativeLattice_mem_iff T hT scale hscale Y A l hl v).mp hv
  rw [← SetLike.mem_coe, derivativeLattice_carrier] at hv'
  obtain ⟨h, r, hr, he⟩ := hv'
  have hh : h = 0 := by
    funext i
    have hi := congrFun hzero i
    change T i * (productEuclideanEquiv.symm v).1 i = 0 at hi
    rw [he] at hi
    change T i * ((h i : ℝ) / T i) = 0 at hi
    rw [mul_div_cancel₀ _ (hT i)] at hi
    exact_mod_cast hi
  subst h
  refine ⟨-r, realDenominatorGrid_neg l hr, ?_⟩
  apply productEuclideanEquiv.symm.injective
  rw [he]
  change derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) 0 r =
    (0, fun j => scale j * A (-r) j)
  simp only [derivativeGridPoint, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe,
    Pi.zero_apply, Int.cast_zero]
  change ((fun i : σ => (0 : ℝ) / T i),
    fun j => scale j * (Y (0 : σ → ℝ) - A r) j) = (0, fun j => scale j * A (-r) j)
  simp only [map_zero, zero_sub, map_neg, Pi.neg_apply, zero_div]
  rfl

end Erdos3

end

end OAI
