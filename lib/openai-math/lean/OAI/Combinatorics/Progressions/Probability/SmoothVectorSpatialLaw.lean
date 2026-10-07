import OAI.Combinatorics.Progressions.Linear.SmoothSpatialKernelRegularity

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def smoothVectorSpatialOutputLaw {D I J N : Type*}
    [Fintype D] [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (M : Matrix I J ℤ) (C : D → Matrix (Unit ⊕ I) N ℤ)
    (H : D → ℝ) (L : ℝ) (Q : D → N → ℝ)
    (hH : ∀ d, 0 < H d) (hL : 0 < L) (hQ : ∀ d j, 0 < Q d j) :
    PMF (D → (Unit ⊕ I) → ℤ) :=
  independentProductPMF (fun d => smoothSpatialOutputLaw root M (C d) (H d) L (Q d) (hH d) hL (hQ d))

theorem smoothVectorSpatialOutputLaw_scaled {D I J N : Type*}
    [Fintype D] [Fintype I] [Fintype J] [Fintype N]
    (root : J → ℤ) (M : Matrix I J ℤ) (C : D → Matrix (Unit ⊕ I) N ℤ)
    (H : D → ℝ) (L : ℝ) (Q : D → N → ℝ)
    (hH : ∀ d, 0 < H d) (hL : 0 < L) (hQ : ∀ d j, 0 < Q d j)
    (v : D → (Unit ⊕ I) → ℤ) :
    (∏ d, ∏ _i : Unit ⊕ I, H d) * (smoothVectorSpatialOutputLaw root M C H L Q hH hL hQ v).toReal =
      ∏ d, ((∏ _i : Unit ⊕ I, H d) *
        (smoothSpatialOutputLaw root M (C d) (H d) L (Q d) (hH d) hL (hQ d) (v d)).toReal) := by
  rw [smoothVectorSpatialOutputLaw, independentProductPMF_toReal, Finset.prod_mul_distrib]

theorem smoothSpatialError_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (B L : ℕ) {ρ ξ : ℝ}
    (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ) : 0 ≤ smoothSpatialError N s B L ρ ξ := by
  unfold smoothSpatialError normalizedFiberErrorConstant integerFiberErrorConstant
    spatialKernelErrorConstant scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

end Erdos3

end

end OAI
