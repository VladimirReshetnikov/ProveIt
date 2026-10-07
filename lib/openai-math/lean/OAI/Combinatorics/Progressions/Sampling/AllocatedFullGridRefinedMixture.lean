import OAI.Combinatorics.Progressions.Estimates.AllocatedRefinedCoverError
import OAI.Combinatorics.Progressions.Lattices.AllocatedFullGridResidueWitness

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "tuples" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  sides (allocatedPrincipalSides_pos B U b S)
local notation "tupleType" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides
local notation "vars" => LayerSamplerVariables G I n B

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (modulus refined : ℕ) (hdiv : modulus ∣ refined)
variable (hperiod : ∀ j : Fin m,
  integerScalarLattice {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)}
    (modulus : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1)
    (Subtype.val : {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} →
      Finset (Fin dim))).mulVecLin.range)
variable (f : ((Σ a : {a : LayerSamplerAxis I n // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) ((Sigma.fst (Subtype.val a)).val + 1)}) → ℝ) → ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S refined) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S refined r.val)

local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
local notation "target" => allocatedSupportedFullGridResidueProfile B U b hR hσ S refined x hb o bW d f witnesses
local notation "conditionalError" r => allocatedSelectedConditionalError (O := rowTypes)
  B U b hR hσ S x (rows) hb o bW d refined
  (AllocatedFullGridResidueWitness.representative (witnesses r))
  (AllocatedFullGridResidueWitness.positive (witnesses r))
  (fun _ => True) f
  (allocatedFullGridSelectedApproximation B U b S rowSets (AllocatedFullGridResidueWitness.expansion (witnesses r)))
  (allocatedFullGridNaturalVolume B U b S rowSets)

include hdiv hperiod f

theorem allocatedSupportedFullGridResidueProfile_refined_error
    (r : AllocatedPositiveResidue (dim := dim) B U b S refined) :
    (fun z => ((tuples).condition _ r.property).complexMean (fun y =>
      (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
        hb o bW d y modulus f z : ℂ)) - target r.val z) = conditionalError r := by
  simp_rw [allocatedWholeMaskedCoveredProfile_refine B U b S x (rows)
    hR hσ hb o bW d _ modulus refined hdiv hperiod f]
  exact allocatedSupportedFullGridResidueProfile_error B U b hR hσ S refined x hb o bW d f witnesses r

variable [NeZero refined]

theorem allocatedFullGridRefinedCover_reconstruction_error
    {X : Type*} [Fintype X]
    (reference : labels → tupleType)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (base : X → ℤ)
    (residue : labels → ColumnResiduePattern (Option vars) X stride)
    (H : X → ℝ) (hH : ∀ t, 0 < H t)
    (hrows : ∀ t, Fintype.card (Option vars) * allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t)
    (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U rowTypes)
    (weight : labels → (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀ r v, v ∈ spatialWindow H 4 → ‖weight r v‖ ≤ C)
    (ε : labels → ℝ)
    (hsampled : ∀ r : AllocatedPositiveResidue (dim := dim) B U b S refined,
      let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r.val)
      let dirs := allocatedPhysicalCubeDirections B U b S x (reference r.val)
      let a := boundedColumnResidueRepresentative stride (residue r.val)
      let cell := columnResiduePattern stride
        (standardPhysicalCubeFrame (physicalCubeRootDifferences root dirs 0 a))
      let V := referenceJetEnvelopeWidths (q := dim) stride H
      (0 < ∑' z, selectedResidueSmoothWeight stride {cell} V z) ∧
      selectedResidueDensityMass stride {cell} V (fun z =>
        ‖(conditionalError r) (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ ε r.val) :
    let reconstruct := fun r => physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r))
      (allocatedPhysicalCubeDirections B U b S x (reference r)) base
      (boundedColumnResidueRepresentative stride (residue r)) stride
    let factor := (3 / 2 : ℝ) ^ Fintype.card (Option (Fin dim) × X) *
      (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := dim) stride H) i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)
    ‖(tuples).complexMean (fun y => ∑ v ∈ spatialWindow H 4,
        weight (principalResidueLabel refined y) v *
          (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
            hb o bW d y modulus f (point (reconstruct (principalResidueLabel refined y) v)) : ℂ)) -
      ((tuples).fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ v ∈ spatialWindow H 4, weight r v * target r (point (reconstruct r v)))‖ ≤
      C * factor * ((tuples).fiberLaw (principalResidueLabel refined)).mean ε := by
  intro reconstruct factor
  apply physicalReconstruction_fiber_error (tuples) (principalResidueLabel refined) stride hs
    (fun r => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r))
    (fun r => allocatedPhysicalCubeDirections B U b S x (reference r)) (fun _ => base)
    residue H hH (fun r t i =>
      (allocatedPhysicalCube_coefficient_row_sum B U b S (fun _ => 0) x (reference r) i).trans (hrows t))
    hscale
    (fun y v => (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
      hb o bW d y modulus f (point v) : ℂ))
    (fun r v => target r (point v)) weight hC hw ε
  intro r hr
  let rr : AllocatedPositiveResidue (dim := dim) B U b S refined := ⟨r, hr⟩
  refine ⟨(hsampled rr).1, ?_⟩
  have he := allocatedSupportedFullGridResidueProfile_refined_error B U b hR hσ S x
    hb o bW d modulus refined hdiv hperiod f witnesses rr
  refine (le_of_eq ?_).trans (hsampled rr).2
  apply congrArg (selectedResidueDensityMass stride _ _)
  funext z
  exact congrArg norm (congrFun he (point (translatePhysicalCube base (standardPhysicalCubeOutput z))))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "tuples" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  sides (allocatedPrincipalSides_pos B U b S)
local notation "tupleType" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides
local notation "vars" => LayerSamplerVariables G I n B

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (modulus refined : ℕ) [NeZero refined] (hdiv : modulus ∣ refined)
variable (hperiod : ∀ j : Fin m,
  integerScalarLattice {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)}
    (modulus : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1)
    (Subtype.val : {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)} →
      Finset (Fin dim))).mulVecLin.range)
variable (f : ((Σ a : {a : LayerSamplerAxis I n // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) ((Sigma.fst (Subtype.val a)).val + 1)}) → ℝ) → ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S refined) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S refined r.val)

local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)
local notation "target" => allocatedSupportedFullGridResidueProfile B U b hR hσ S refined x hb o bW d f witnesses
local notation "conditionalError" r => allocatedSelectedConditionalError (O := rowTypes)
  B U b hR hσ S x (rows) hb o bW d refined
  (AllocatedFullGridResidueWitness.representative (witnesses r))
  (AllocatedFullGridResidueWitness.positive (witnesses r))
  (fun _ => True) f
  (allocatedFullGridSelectedApproximation B U b S rowSets (AllocatedFullGridResidueWitness.expansion (witnesses r)))
  (allocatedFullGridNaturalVolume B U b S rowSets)

include hdiv hperiod f

theorem allocatedFullGridRefinedCover_selected_reconstruction_error
    {X : Type*} [Fintype X]
    (reference : labels → tupleType)
    (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option vars) X stride))
    (V₀ : Option vars × X → ℝ) (hV₀ : ∀ z, 0 < V₀ z)
    (hZ₀ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z)
    (H : X → ℝ) (hH : ∀ t, 0 < H t)
    (T : X → ℝ) {W L : ℝ} (hL : L ≠ 0) (hRatio : ∀ t, H t = (1 + W) * T t)
    (hA : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) L i)
    (hrows : ∀ t, Fintype.card (Option vars) * allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t)
    (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U rowTypes)
    (weight : labels → cells → (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    {C Z : ℝ} (hC : 0 ≤ C) (hZ : 0 < Z)
    (hw : ∀ r a v, v ∈ spatialWindow H 4 → ‖weight r a v‖ ≤
      C / (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) L i))
    (ε : labels → ℝ)
    (hsampled : ∀ (a : cells) (r : AllocatedPositiveResidue (dim := dim) B U b S refined),
      let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r.val)
      let dirs := allocatedPhysicalCubeDirections B U b S x (reference r.val)
      let cell := columnResiduePattern stride (standardPhysicalCubeFrame
        (physicalCubeRootDifferences root dirs 0 (boundedColumnResidueRepresentative stride a.val)))
      let V := referenceJetEnvelopeWidths (q := dim) stride H
      (0 < ∑' z, selectedResidueSmoothWeight stride {cell} V z) ∧
      selectedResidueDensityMass stride {cell} V (fun z =>
        ‖(conditionalError r) (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ ε r.val) :
    let reconstruct := fun r (a : cells) => physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r))
      (allocatedPhysicalCubeDirections B U b S x (reference r)) base
      (boundedColumnResidueRepresentative stride a.val) stride
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    ‖((tuples).complexMean (fun y => ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
        ∑ v ∈ spatialWindow H 4, weight (principalResidueLabel refined y) a v *
          (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
            hb o bW d y modulus f (point (reconstruct (principalResidueLabel refined y) a v)) : ℂ)) -
      ((tuples).fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a v)))) / (Z : ℂ)‖ ≤
      (C * factor * ((tuples).fiberLaw (principalResidueLabel refined)).mean ε) / Z := by
  intro reconstruct factor
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) L i
  let E := C * factor * ((tuples).fiberLaw (principalResidueLabel refined)).mean ε
  have hcancel : (C / A) * ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin dim) × X) *
      (∏ i, residueProfileWidth stride (referenceJetEnvelopeWidths (q := dim) stride H) i) /
      (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) = C * factor := by
    rw [referenceJetEnvelope_anisotropic_volume stride hs H T hL hRatio]
    change (C / A) * (factor * A) = C * factor
    field_simp [show A ≠ 0 from hA.ne']
  have heach (a : cells) := (allocatedFullGridRefinedCover_reconstruction_error
    B U b hR hσ S x hb o bW d modulus refined hdiv hperiod f witnesses reference
    stride hs base (fun _ => a.val) H hH hrows hscale point
    (fun r => weight r a) (div_nonneg hC hA.le) (fun r => hw r a) ε (hsampled a)).trans_eq
      (congrArg (fun c => c * ((tuples).fiberLaw (principalResidueLabel refined)).mean ε) hcancel)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  apply div_le_div_of_nonneg_right _ hZ.le
  rw [(tuples).complexMean_sum, ((tuples).fiberLaw (principalResidueLabel refined)).complexMean_sum]
  simp_rw [FiniteProbabilityWeights.complexMean_mul_left]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ a : cells, ‖(selectedResidueCellWeight stride cells V₀ a : ℂ) *
        ((tuples).complexMean (fun y => ∑ v ∈ spatialWindow H 4,
          weight (principalResidueLabel refined y) a v *
            (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
              hb o bW d y modulus f (point (reconstruct (principalResidueLabel refined y) a v)) : ℂ)) -
        ((tuples).fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a v))))‖ := norm_sum_le _ _
    _ ≤ ∑ a : cells, selectedResidueCellWeight stride cells V₀ a * E := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (selectedResidueCellWeight_nonneg _ _ _ a)]
      exact mul_le_mul_of_nonneg_left (heach a) (selectedResidueCellWeight_nonneg _ _ _ a)
    _ = E := by
      rw [← Finset.sum_mul, selectedResidueCellWeight_sum stride cells V₀ hV₀ hZ₀, one_mul]

end Erdos3.VectorPolynomial

end

end OAI
