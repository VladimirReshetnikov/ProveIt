import OAI.Combinatorics.Progressions.Estimates.EuclideanDerivativeCovolume

namespace OAI

section

namespace Erdos3

open Module

theorem euclideanDerivative_covolume_density_bound
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ)) :
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T (fun i => (hT i).ne') scale hscale Y A l hl
    let d := finrank ℝ (shortVectorSpan Λ ρ)
    ZLattice.covolume (shortVectorLattice Λ ρ) ≤
      (((d : ℝ) + 2) * ρ) ^ d / (δ * ∏ i, T i) := by
  obtain ⟨P, hcard, hP⟩ := exists_bounded_derivativeGridPoint_family T
    (fun i => (hT i).ne') scale Y (LinearMap.toMatrix' A.toLinearMap) l H 0 R
    (fun h hh => ⟨r h, hr h hh, by simpa only [sub_zero] using hnorm h hh⟩)
  apply euclideanDerivativeLattice_covolume_le T (fun i => (hT i).ne') scale hscale
    Y A l hl R (δ * ∏ i, T i) hR (mul_pos hδ (Finset.prod_pos (fun i _ => hT i))) P hP
  simpa only [hcard] using hdense

end Erdos3

end

end OAI
