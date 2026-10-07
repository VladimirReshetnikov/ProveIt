import OAI.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
private theorem slicedBlock_det_ne_zero (second : Bool) :
    (fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fixedSpatialKernelSliceFrame Wsp Lsp slice.path.normalizedNoise
        slice.kernelLower slice.kernelWidth) second).det ≠ 0 := by
  have hbase : (fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise second).det ≠ 0 := by
    cases second
    · exact slice.path.detFalse
    · exact slice.path.detTrue
  let w : X → ℝ := fun i => slice.kernelWidth
    (spatialEquiv.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))
  have hmatrix : fixedSpatialKernelBlock spatialEquiv Wsp Lsp
      (fixedSpatialKernelSliceFrame Wsp Lsp slice.path.normalizedNoise
        slice.kernelLower slice.kernelWidth) second =
      fixedSpatialKernelBlock spatialEquiv Wsp Lsp slice.path.normalizedNoise second * Matrix.diagonal w := by
    ext x i
    rw [fixedSpatialKernelBlock_slice, Matrix.mul_diagonal]
  rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero hbase (Finset.prod_ne_zero_iff.mpr (fun i _ => slice.kernelWidth_ne_zero _))

noncomputable def slicedBlockEquiv (second : Bool) : (X → ℝ) ≃L[ℝ] (X → ℝ) :=
  fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
    (fixedSpatialKernelSliceFrame Wsp Lsp slice.path.normalizedNoise
      slice.kernelLower slice.kernelWidth) second (slice.slicedBlock_det_ne_zero second)

theorem density_bounds
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) (hδslice : 0 < δslice) :
    (∀ y, ‖slice.density hBactive y‖ ≤
      (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) hδslice : ℝ)) ∧
    LipschitzWith (fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
      (slice.slicedBlockEquiv true) hδslice) (slice.density hBactive) := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  have h := fixedSpatialKernelSliceOriginalForecastDensity_bounds B U b hR hσ S
    spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth
    slice.path.detFalse slice.path.detTrue slice.kernelWidth_ne_zero hBactive
    slice.path.lower slice.path.width hδslice slice.path.hwidth slice.path.hlower
    slice.path.sample slice.path.hs
  refine ⟨?_, h.2⟩
  intro y
  change ‖fixedSpatialKernelSliceOriginalForecastDensity B U b S
    spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth
    slice.path.detFalse slice.path.detTrue slice.kernelWidth_ne_zero hBactive
    slice.path.lower slice.path.width slice.path.sample y‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (h.1 y).1]
  exact (h.1 y).2

theorem density_active_support
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) (hδslice : 0 < δslice)
    (y : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
      ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) → ℝ)))
    (hy : slice.density hBactive y ≠ 0)
    (a : Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}, Unit) :
    |y.2 a| ≤ 3 := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  have hnorm : ‖y.2‖ ≤ 2 := by
    by_contra! h
    exact hy (fixedSpatialKernelSliceOriginalForecastDensity_zero_of_active_norm_gt_two
      B U b hR hσ S spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth
      slice.path.detFalse slice.path.detTrue slice.kernelWidth_ne_zero hBactive
      slice.path.lower slice.path.width hδslice slice.path.hwidth slice.path.hlower
      slice.path.sample slice.path.hs slice.path.hcontained y h)
  have hcoord : |y.2 a| ≤ ‖y.2‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y.2 a
  linarith

omit [Fintype Tsp] in

theorem slicedBlock_inverse_bounds {v : ℝ} (hv : 0 ≤ v)
    (hwidth : ∀ g, Real.exp (-v) ≤ slice.kernelWidth g) :
    inverseJacobian (slice.slicedBlockEquiv true) ≤
        Real.exp (P + (Fintype.card X + 1) * v) ∧
      ‖(slice.slicedBlockEquiv false).symm.toContinuousLinearMap‖ ≤
        Real.exp (P + (Fintype.card X + 1) * v) := by
  have hj := fixedSpatialKernelBlockEquiv_slice_inverseJacobian_le
    spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth true
    slice.path.detTrue (slice.slicedBlock_det_ne_zero true) (Real.exp_pos (-v)) hwidth
  have hi := fixedSpatialKernelBlockEquiv_slice_inverse_norm_le
    spatialEquiv Wsp Lsp slice.path.normalizedNoise slice.kernelLower slice.kernelWidth false
    slice.path.detFalse (slice.slicedBlock_det_ne_zero false) (Real.exp_pos (-v)) hwidth
  have hexp : (Real.exp (-v))⁻¹ = Real.exp v := by rw [Real.exp_neg, inv_inv]
  rw [hexp] at hj hi
  constructor
  · calc
      _ ≤ Real.exp v ^ Fintype.card X * inverseJacobian
          (fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp slice.path.normalizedNoise true slice.path.detTrue) := hj
      _ ≤ Real.exp v ^ Fintype.card X * Real.exp P :=
        mul_le_mul_of_nonneg_left slice.path.hjac (pow_nonneg (Real.exp_nonneg _) _)
      _ = Real.exp (P + Fintype.card X * v) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  · calc
      _ ≤ Real.exp v * ‖(fixedSpatialKernelBlockEquiv spatialEquiv Wsp Lsp
          slice.path.normalizedNoise false slice.path.detFalse).symm.toContinuousLinearMap‖ := hi
      _ ≤ Real.exp v * Real.exp P := mul_le_mul_of_nonneg_left slice.path.hinverse (Real.exp_nonneg _)
      _ = Real.exp (P + v) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ Fintype.card X from Nat.cast_nonneg _])

theorem density_uniform_budget
    (hBactive : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val))
    (hP : 1 ≤ P) (hδslice : 0 < δslice) (hδinv : δslice⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    {v : ℝ} (hv : 0 ≤ v) (hwidth : ∀ g, Real.exp (-v) ≤ slice.kernelWidth g) :
    let Ps := P + (Fintype.card X + 1) * v
    (fixedSpatialOriginalForecastCap B (slice.slicedBlockEquiv true) hδslice : ℝ) + 1 ≤
        Real.exp (forecastOriginalSmoothBudget m Ps) ∧
      (fixedSpatialOriginalForecastLip B (slice.slicedBlockEquiv false)
        (slice.slicedBlockEquiv true) hδslice : ℝ) ≤ Real.exp (forecastOriginalSmoothBudget m Ps) ∧
      (∀ y, ‖slice.density hBactive y‖ ≤ Real.exp (forecastOriginalSmoothBudget m Ps)) ∧
      LipschitzWith (Real.toNNReal (Real.exp (forecastOriginalSmoothBudget m Ps)))
        (slice.density hBactive) := by
  intro Ps
  have hPPs : P ≤ Ps := by
    dsimp only [Ps]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hv)
  obtain ⟨hjac, hinverse⟩ := slice.slicedBlock_inverse_bounds hv hwidth
  obtain ⟨hcap, hlip⟩ := fixedSpatialOriginalForecast_uniform_budget B
    (slice.slicedBlockEquiv false) (slice.slicedBlockEquiv true) (hP.trans hPPs) hδslice
    (hδinv.trans (Real.exp_le_exp.mpr hPPs)) (hX.trans hPPs)
    (haxes.trans hPPs) (hblocks.trans hPPs) hjac hinverse
  obtain ⟨hbound, hlipschitz⟩ := slice.density_bounds hBactive hδslice
  refine ⟨hcap, hlip, fun y => (hbound y).trans (by linarith), ?_⟩
  apply hlipschitz.weaken
  exact NNReal.coe_le_coe.mp (by simpa only [Real.coe_toNNReal _ (Real.exp_nonneg _)] using hlip)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
