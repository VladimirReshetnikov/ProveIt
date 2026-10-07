import OAI.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice

namespace OAI

section

namespace Erdos3

theorem euclideanDerivativeLattice_shortSpan_projection
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T
      (fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne') scale hscale Y A l hl
    (shortVectorSpan Λ ρ).map ((LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp
      productEuclideanEquiv.symm.toLinearMap) = ⊤ := by
  let hT0 : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T (fun i => (hT0 i).ne') scale hscale Y A l hl
  let π₀ := (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)).comp productEuclideanEquiv.symm.toLinearMap
  let e := coordinateScaleEquiv T (fun i => (hT0 i).ne')
  let π := e.toLinearMap.comp π₀
  have hspan := integer_points_span_eq_top_of_density H T R δ hT hR
    (fun h hh => derivativeGridPoint_shift_bound T hT0 scale Y _ h (r h) R (hnorm h hh))
    hdense hlarge
  have hmap : (shortVectorSpan Λ ρ).map π = ⊤ := by
    apply shortVectorSpan_map_eq_top_of_spanning_integer_images Λ π H ρ hspan
    intro h hh
    let v := derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)
    refine ⟨productEuclideanEquiv v, ?_, ?_, ?_⟩
    · apply (productEuclideanEquiv_mem_derivativeLattice T
        (fun i => (hT0 i).ne') scale hscale Y A l hl v).mpr
      rw [← SetLike.mem_coe, derivativeLattice_carrier]
      exact derivativeGridPoint_mem T scale Y _ l h (r h) (hr h hh)
    · exact (productEuclideanEquiv_norm_le v).trans
        (mul_le_mul_of_nonneg_left (hnorm h hh) (Nat.cast_nonneg _))
    · change e (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)
        (productEuclideanEquiv.symm (productEuclideanEquiv v))) = _
      rw [LinearEquiv.symm_apply_apply]
      funext i
      exact mul_div_cancel₀ (h i : ℝ) (hT0 i).ne'
  have hmap' : ((shortVectorSpan Λ ρ).map π₀).map e.toLinearMap = ⊤ := by
    simpa only [← Submodule.map_comp] using hmap
  exact (Submodule.map_eq_top_iff (e := e)).mp hmap'

end Erdos3

end

end OAI
