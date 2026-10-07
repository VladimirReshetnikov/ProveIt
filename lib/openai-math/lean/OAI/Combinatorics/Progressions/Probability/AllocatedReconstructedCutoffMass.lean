import OAI.Combinatorics.Progressions.Sampling.AllocatedTranslatedCutoffSampling

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable {X : Type*} [Fintype X]
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (stride N : X → ℕ) (hs : ∀ t, 0 < stride t) (hN : ∀ t, 0 < N t)
variable (modulus : ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value) (base : X → ℤ)
variable {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N stride
local notation "T" => trimmedSpatialSlopeScale W τ N stride
local notation "envelope" => referenceJetEnvelopeWidths (q := dim) stride H
local notation "volume" => (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i)
local notation "factor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X)
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "point" => physicalCubeRowSample U d rows p hm
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride))

include hs hN hW hτ in
theorem allocatedNormalizedCutoff_reconstructed_cell_mass {M : ℝ}
    (hrows : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t)
    (href : ∀ cell : ColumnResiduePattern (Option (Fin dim)) X stride,
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {cell} envelope z,
        selectedResidueDensityMass stride {cell} envelope
          (fun z => amp * ‖cutoff (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ M)
    (label : labels) (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride) :
    (∑ v ∈ spatialWindow H 4, amp * ‖cutoff (point
      (allocatedWholeResidueReconstruction B U b S X modulus stride wholeReference x base label a v))‖) / volume ≤
      factor * M := by
  let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
  let dirs := allocatedPhysicalCubeDirections B U b S x (wholeReference label)
  have hpos (t : X) := trimmedSpatial_scales_pos hW hτ N stride t (hN t) (hs t)
  exact physicalReconstruction_normalized_mass_le stride hs root dirs a base H T
    (fun t => (hpos t).1) (fun t => (hpos t).2) hW (Nat.cast_pos.mpr S.positive)
    (trimmedSpatial_scale_ratio hW N stride)
    (fun t i => (allocatedPhysicalCube_coefficient_row_sum B U b S (fun _ => 0) x
      (wholeReference label) i).trans (hrows t)) hscale
    (fun v => amp * ‖cutoff (point v)‖) (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (href _)

include hs hN hW hτ in
theorem allocatedNormalizedCutoff_recentered_mass {M ξ : ℝ} (hξ : 0 < ξ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (hrows : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t)
    (href : ∀ cell : ColumnResiduePattern (Option (Fin dim)) X stride,
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {cell} envelope z,
        selectedResidueDensityMass stride {cell} envelope
          (fun z => amp * ‖cutoff (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ M) :
    (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mean
      (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ) B U b S X modulus stride
        wholeReference x N base cells point (fun _ y => ((amp * ‖cutoff y‖ : ℝ) : ℂ))) ≤ factor * M := by
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  have hV : ∀ z, 0 < V z := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
  have hnorm (y : EuclideanJetLayers U rowTypes) : ‖((amp * ‖cutoff y‖ : ℝ) : ℂ)‖ = amp * ‖cutoff y‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hlocal (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)) :
      allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ) B U b S X modulus stride
        wholeReference x N base cells point (fun _ y => ((amp * ‖cutoff y‖ : ℝ) : ℂ)) y ≤ factor * M := by
    change (∑ a : cells, selectedResidueCellWeight stride cells V a *
      ((∑ v ∈ spatialWindow H 4, ‖((amp * ‖cutoff (point
        (allocatedWholeResidueReconstruction B U b S X modulus stride wholeReference x base
          (principalResidueLabel (residueRefinedPeriod modulus stride) y) a.val v))‖ : ℝ) : ℂ)‖) / volume)) ≤ _
    simp only [hnorm]
    calc
      _ ≤ ∑ a : cells, selectedResidueCellWeight stride cells V a * (factor * M) := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left
          (allocatedNormalizedCutoff_reconstructed_cell_mass B U b S rowSets o hb bW d r hr p hm
            stride N hs hN modulus wholeReference x base hW hτ hrows hscale href _ a.val)
          (selectedResidueCellWeight_nonneg stride cells V a)
      _ = factor * M := by
        rw [← Finset.sum_mul, selectedResidueCellWeight_sum stride cells V hV hZ, one_mul]
  exact ((principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mean_mono hlocal).trans_eq
    (FiniteProbabilityWeights.mean_const _ _)

end Erdos3.BooleanCubeKernel

end

end OAI
