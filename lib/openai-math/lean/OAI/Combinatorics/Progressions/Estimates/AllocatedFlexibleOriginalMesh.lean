import OAI.Combinatorics.Progressions.Estimates.AllocatedCommonCover
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalPrescribedMesh
import OAI.Combinatorics.Progressions.Estimates.AllocatedUniformReferencePrescribed

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

def AllocatedReferenceSelectedIdealAt (D Psp E e t : ℝ) (δ : ℝ≥0) (K : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp E
  let gainLog := allocatedProfileGainLog m D Psp w
  ∀ (_hmPsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t)
    {pNum : ℝ} (_hPspNum : Psp ≤ pNum)
    (_hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp pNum)
    (_herrorNum : profileReferenceErrorLog Psp E ≤ pNum)
    (_hRefineNum : (m + 1 : ℕ) * Psp + Psp ^ 2 + (dim + 1 : ℕ) ≤ pNum)
    (_hRP : ∀ j, R j ≤ Real.exp pNum) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pNum)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp pNum),
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    modulus ≤ Mk ^ (m + 1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range) ∧
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type*} [Fintype X] [DecidableEq X]
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    (∀ (hσ1 : ∀ j, σ j ≤ 1) u r (z : AllocatedLongJetRows B U b S jets),
      |(allocatedLongResidueWeights B U b S refined hRefined r hsize).mean
          (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := jets) a) *
            allocatedLongJetDensity B U b hR hσ S x u v jetRows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u jetRows s hA modulus (residue u r) z| ≤
          physicalIdealErrorShare error (allocatedIdealVolumeEnvelope m D pNum)) ∧
    AllocatedFixedDataSourceAt B U b hR hσ S x jetRows X hMk selection hx modulus s hA
      q reference residue hb o bW d
      (physicalIdealErrorShare error (allocatedIdealVolumeEnvelope m D pNum)) ∧
    ∀ (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {Rrank : ℝ}
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (_hτP : 1 / τ ≤ Real.exp pNum)
    (spatialMesh : ℝ) (_hspatialMesh : 0 < spatialMesh)
    {Dsp : ℝ}
    (_hDsp : Dsp ≤ Real.exp Psp) (_hWscale : W ≤ Dsp * (S.value : ℝ)),
    let input := allocatedActualProfileInput m D pNum e gainLog lengthLog
    let Pout := allocatedProfileFourierOutput input
    (∀ a, Real.exp ((Pout + K) ^ K) ≤ (N a : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun a => (N a : ℝ)) Rrank (U j) (p j)) →
    Real.exp ((Pout + K) ^ K) ≤ Rrank →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ w, ‖test w‖ ≤ 1) →
    ∀ Z : ℝ, 1 / 2 ≤ Z →
    allocatedRefinedReferenceTailBound (τ := τ) (ξ := ξ)
      B U b hR hσ S x jetRows X hMk selection hx modulus q reference hb o bW d
      N _hW spatialMesh base cells (physicalCubeEuclideanSample U d p hm) test
      (physicalIdealErrorShare error (allocatedIdealVolumeEnvelope m D pNum))
      (Z * Real.exp (-E)) ∧
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus s hA q reference residue hb o bW d
        N _hW spatialMesh base cells (physicalCubeEuclideanSample U d p hm) test Z -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus q reference residue hb o bW d
        N _hW spatialMesh base cells (physicalCubeEuclideanSample U d p hm) test Z δ‖ ≤ Real.exp (-E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))
local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_reference_chosen_ideal
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {D Psp E : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) :
    ∃ K : ℕ, 2 ≤ K ∧
      let target := profileReferenceErrorLog Psp E
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) hLayer A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          AllocatedReferenceChosenIdealAt.{_, _, _, uGeom, uCover, uSpace}
            (G := G) (dim := dim) B D Psp E e t δ K := by
  let target := profileReferenceErrorLog Psp E
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    dsimp [target, profileReferenceErrorLog]
    linarith
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have he : 0 ≤ physicalIdealSmoothingLog (B := B)
      (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
      hLayer A T target (allocatedProfileGainLog m D Psp w) :=
    physicalIdealSmoothingLog_nonneg hLayer A T htarget hgain
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    exists_allocated_reference_actual_ideal (G := G) (dim := dim)
      B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1,
    allocatedReferenceActualIdealAt_chooseScale B hdim hPsp hE he hcompare⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))
local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_reference_prescribed_ideal
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {D Psp E : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) :
    ∃ K : ℕ, 2 ≤ K ∧
      let target := profileReferenceErrorLog Psp E
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) hLayer A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          AllocatedReferencePrescribedIdealAt.{_, _, _, uGeom, uCover, uSpace}
            (G := G) (dim := dim) B D Psp E e t δ K := by
  let target := profileReferenceErrorLog Psp E
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    dsimp [target, profileReferenceErrorLog]
    linarith
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have he : 0 ≤ physicalIdealSmoothingLog (B := B)
      (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
      hLayer A T target (allocatedProfileGainLog m D Psp w) :=
    physicalIdealSmoothingLog_nonneg hLayer A T htarget hgain
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    exists_allocated_reference_chosen_ideal (G := G) (dim := dim)
      B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE
  obtain ⟨Ktail, hKtail, htail⟩ :=
    exists_allocated_ideal_reference_tail.{uG, uI, uB, uGeom, uCover, uSpace} m dim
  exact ⟨max K Ktail, hK.trans (le_max_left _ _), δ, hδ, hδ1, hδeq, hδe, ht, ht1,
    allocatedReferenceChosenIdealAt_prescribeData B hdim hPsp hE he hK hKtail htail hcompare⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

theorem allocatedReferenceChosenIdealAt_selectData
    {D Psp E e t : ℝ} {δ : ℝ≥0} {K Ktail : ℕ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e)
    (hK : 2 ≤ K) (hKtail : 2 ≤ Ktail)
    (htail : AllocatedIdealReferenceTailAt.{uG, uI, uB, uGeom, uCover, uSpace} m dim Ktail)
    (hcompare : AllocatedReferenceChosenIdealAt.{_, _, _, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t δ K) :
    AllocatedReferenceSelectedIdealAt.{_, _, _, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t δ (max K Ktail) := by
  have hprescribed := allocatedReferenceChosenIdealAt_prescribeData B hdimensions
    hPsp hE he hK hKtail htail hcompare
  intro hmPsp hdimPsp hGPsp J _ U b R σ hR hσ hσt pNum hPspNum hcount
    herrorNum hRefineNum hRP hRi hσi
  obtain ⟨hS, hdata⟩ := hprescribed hmPsp hdimPsp hGPsp U b hR hσ hσt
    hPspNum hcount herrorNum hRefineNum hRP hRi hσi
  refine ⟨hS, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨modulus, hmodulus, hmodulusM, hspatial, hperiod⟩ :=
    goodKernel_common_period selection x hx (m + 1) (by omega)
      (fun j : Fin m => j.val + 1) (fun j => by omega) jetRows
      (fun _ => Subtype.val_injective) (fun _ z => z.property)
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  exact ⟨modulus, hmodulus, hmodulusM, hspatial, hperiod,
    hdata x hMk selection hx hqDim hMkPsp modulus hmodulus hmodulusM hspatial hperiod⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

def AllocatedCommonReferenceAt (p Psp E e t : ℝ) (δ : ℝ≥0) (K : ℕ) : Prop :=
  ∀ {c : ℝ} (_hc : 0 ≤ c) {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t) (_hR1 : ∀ j, R j ≤ 1)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c),
    AllocatedReferenceAtScale.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim) B U b hR hσ
      (allocatedComparisonDimension m p) Psp E e (allocatedCommonScaleNumeric m p c Psp E) δ K

theorem allocatedReferencePrescribedIdealAt_commonScale
    {p Psp E e t : ℝ} {δ : ℝ≥0} {K : ℕ}
    (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hcompare : AllocatedReferencePrescribedIdealAt.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B (allocatedComparisonDimension m p) Psp E e t δ K) :
    AllocatedCommonReferenceAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim) B p Psp E e t δ K := by
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  obtain ⟨hq, _, hcq, hPq, hcountq, herrorq, hrefineq⟩ :=
    allocatedCommonScaleNumeric_bounds m hp hc hPsp hE
  have hdim' : ((dim + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by
    exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
  have hm' : ((m + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast (show m + 1 ≤ m + 2 by omega)
  have hG : (Fintype.card G : ℝ) ≤ Psp :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hvars.trans hpPsp)
  have hcount := allocatedSiteScale_coefficient_count B hp hvars
  exact hcompare (hm'.trans hmPsp) (hdim'.trans hmPsp) hG U b hR hσ hσt
    hPq (fun j => (hcount j).trans (Real.exp_le_exp.mpr hcountq)) herrorq
    (by linarith) (fun j => (hR1 j).trans (Real.one_le_exp_iff.mpr hq))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hcq))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hcq))

theorem exists_allocated_common_reference
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {p Psp E : ℝ} (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    ∃ K : ℕ, 2 ≤ K ∧
      let D := allocatedComparisonDimension m p
      let target := profileReferenceErrorLog Psp E
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
          (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          AllocatedCommonReferenceAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim) B p Psp E e t δ K := by
  have hdimensions := allocatedComparisonDimensions_of_primitive B jetRows
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) hp hvars hI hn
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    exists_allocated_reference_prescribed_ideal.{uG,uI,uB,uGeom,uCover,uSpace} B
      ψ hψ hrange hzero hone A T hLip hTransition hdimensions hPsp hE
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1,
    allocatedReferencePrescribedIdealAt_commonScale B hp hPsp hE hdim hmPsp hpPsp hvars hcompare⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))
local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_reference_selected_ideal
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {D Psp E : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) :
    ∃ K : ℕ, 2 ≤ K ∧
      let target := profileReferenceErrorLog Psp E
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) hLayer A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          AllocatedReferenceSelectedIdealAt.{_, _, _, uGeom, uCover, uSpace}
            (G := G) (dim := dim) B D Psp E e t δ K := by
  let target := profileReferenceErrorLog Psp E
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    dsimp [target, profileReferenceErrorLog]
    linarith
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have he : 0 ≤ physicalIdealSmoothingLog (B := B)
      (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
      hLayer A T target (allocatedProfileGainLog m D Psp w) :=
    physicalIdealSmoothingLog_nonneg hLayer A T htarget hgain
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    exists_allocated_reference_chosen_ideal (G := G) (dim := dim)
      B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE
  obtain ⟨Ktail, hKtail, htail⟩ :=
    exists_allocated_ideal_reference_tail.{uG, uI, uB, uGeom, uCover, uSpace} m dim
  exact ⟨max K Ktail, hK.trans (le_max_left _ _), δ, hδ, hδ1, hδeq, hδe, ht, ht1,
    allocatedReferenceChosenIdealAt_selectData B hdim hPsp hE he hK hKtail htail hcompare⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

def AllocatedCommonOriginalMeshAt (p Psp E e t : ℝ) (δ : ℝ≥0) (A T Kproj Kideal : ℕ) : Prop :=
  ∀ {c : ℝ} (_hc : 0 ≤ c) {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t) (_hR1 : ∀ j, R j ≤ 1)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c),
    AllocatedOriginalPrescribedMeshAtScale.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim) B U b hR hσ
      (allocatedComparisonDimension m p) Psp E e (allocatedCommonScaleNumeric m p c Psp (E + 4)) δ A T Kproj Kideal

theorem allocatedOriginalPrescribedMeshAt_commonScale
    {p Psp E e t : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (horiginal : AllocatedOriginalPrescribedMeshAt.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B (allocatedComparisonDimension m p) Psp E e t δ A T Kproj Kideal) :
    AllocatedCommonOriginalMeshAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim)
      B p Psp E e t δ A T Kproj Kideal := by
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  have hE4 : 0 ≤ E + 4 := by linarith
  obtain ⟨hq, _, hcq, hPq, hcountq, herrorq, hrefineq⟩ :=
    allocatedCommonScaleNumeric_bounds m hp hc hPsp hE4
  have hdim' : ((dim + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by
    exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
  have hm' : ((m + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast (show m + 1 ≤ m + 2 by omega)
  have hG : (Fintype.card G : ℝ) ≤ Psp :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hvars.trans hpPsp)
  have hvarsGrowth : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Psp :=
    (hvars.trans hpPsp).trans (by linarith [Real.add_one_le_exp Psp])
  have hcount := allocatedSiteScale_coefficient_count B hp hvars
  exact horiginal (hm'.trans hmPsp) (hdim'.trans hmPsp) hG hvarsGrowth U b hR hσ hσt
    hPq (fun j => (hcount j).trans (Real.exp_le_exp.mpr hcountq)) herrorq
    (by linarith) (fun j => (hR1 j).trans (Real.one_le_exp_iff.mpr hq))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hcq))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hcq))

theorem exists_allocated_common_original_mesh
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {p Psp E : ℝ} (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    ∃ K : ℕ, 2 ≤ K ∧
      let D := allocatedComparisonDimension m p
      let target := profileReferenceErrorLog Psp (E + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
          (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∃ A₀ T₀ Kproj : ℕ, 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
            AllocatedCommonOriginalMeshAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim)
              B p Psp E e t δ A₀ T₀ Kproj K := by
  have hdimensions := allocatedComparisonDimensions_of_primitive B jetRows
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) hp hvars hI hn
  have hE4 : 0 ≤ E + 4 := by linarith
  have htarget : 0 ≤ profileReferenceErrorLog Psp (E + 4) := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    unfold profileReferenceErrorLog
    linarith
  have hw : 0 ≤ (m * 2 ^ (m + 1) : ℕ) * Psp := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdimensions.nonneg hPsp hw
  have he := physicalIdealSmoothingLog_nonneg (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    (layerSamplerDegree I n) A T htarget hgain
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    exists_allocated_reference_prescribed_ideal.{uG,uI,uB,uGeom,uCover,uSpace} B
      ψ hψ hrange hzero hone A T hLip hTransition hdimensions hPsp hE4
  obtain ⟨A₀, T₀, Kproj, hA₀, hT₀, hKproj, horiginal⟩ :=
    allocatedReferencePrescribedIdealAt_original_mesh B hdimensions hPsp hE he ht1 hK hcompare
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
    allocatedOriginalPrescribedMeshAt_commonScale B hp hPsp hE hdim hmPsp hpPsp hvars horiginal⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

section FixedScale

variable {J : Fin m → Type uGeom} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

def AllocatedOriginalResidueWeightedMeshAtScale (D Psp E e pNum : ℝ) (δ : ℝ≥0)
    (A T Kproj Kideal : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp (E + 4)
  let gainLog := allocatedProfileGainLog m D Psp w
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let l := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Q := allocatedSourceSamplingBudget m dim A Pbase E l F
  let K := max T (max Kproj Kideal)
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp),
  ∃ (d : ℕ) (hd : 0 < d),
    let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((Pbase + A) ^ A) ∧
  ∀ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (_hmodulusSize : modulus ≤ Mk ^ (m + 1))
      (_hspatialPeriod : ∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
      (_hcoefficientPeriod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range),
    ∃ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0),
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ))) ∧
    ∀ (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Kcov : Fin m → Type uCover} [∀ j, Fintype (Kcov j)]
    (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type uSpace} [Fintype X] [DecidableEq X]
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (q : X → ℕ) (_hq : ∀ t, 0 < q t) (_hqPsp : ∀ t, (q t : ℝ) ≤ Real.exp Psp),
    let refined := residueRefinedPeriod modulus q
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp + Fintype.card X * Psp) ∧
    ∃ hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) a,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j) ∧
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let hW := allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)
    let indices := PrincipalTupleIndex B (layerSamplerDegree I n)
    let ξ := normalizedTupleNarrowWidth X indices selection Mk Psp (E + 2)
    let hξ := normalizedTupleNarrowWidth_pos X indices selection Mk Psp (E + 2)
    let mesh := normalizedTupleRadius X selection Mk Psp (E + 2) W / 4
    ∀ (small : ℝ) (_hsmall : 0 < small) (_hsmallMesh : small ≤ mesh)
    {τ : ℝ} (hτ : 0 < τ) (_hτP : 1 / τ ≤ Real.exp pNum)
    (N : X → ℕ) (hN : ∀ t, 0 < N t)
    (_hsize : ∀ t, Real.exp ((Q + K) ^ K) ≤ (N t : ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    {rank : ℝ}
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) rank (U j) (poly j))
    (_hRank : Real.exp ((Q + K) ^ K) ≤ rank)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hcells : cells.Nonempty)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (_htest : ∀ site v, ‖test site v‖ ≤ 1)
    (Z : ℝ) (_hZ : 1 / 2 ≤ Z),
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N) z,
    ‖allocatedOriginalTupleSource B U b hR hσ S x X q hb o N hN hW hτ hξ base cells hmass
        (physicalCubeSiteTest test) Z poly hmem -
      allocatedWholeIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus q reference hb o bW d
        N hW small base cells (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z δ‖ ≤
      Real.exp (-E)

theorem allocatedOriginalPrescribedMeshAtScale_residue_weighted
    {D Psp E e pNum : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (horiginal : AllocatedOriginalPrescribedMeshAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B U b hR hσ D Psp E e pNum δ A T Kproj Kideal) :
    AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B U b hR hσ D Psp E e pNum δ A T Kproj Kideal := by
  unfold AllocatedOriginalResidueWeightedMeshAtScale
  intro w error gainLog S lengthLog Pbase l F Q K
  obtain ⟨hS, horiginal⟩ := horiginal
  refine ⟨hS, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, horiginal⟩ := horiginal x hMk selection hx hqDim hMkPsp
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro modulus hmodulus
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  intro _ hmodulusSize hspatialPeriod hcoefficientPeriod
  obtain ⟨s, hA, hinverse, horiginal⟩ := horiginal modulus hmodulus
    hmodulusSize hspatialPeriod hcoefficientPeriod
  refine ⟨s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ _ _ ν _ _
    X _ _ hXPsp q hq hqPsp refined
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, horiginal⟩ :=
    horiginal block hb o bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ mesh small hsmallMeshPos hsmallMesh τ hτ hτP N hN hsizeN poly hpoly hmem rank hrank hRank
    base cells hcells test htest Z hZ
  obtain ⟨hmass, he⟩ := horiginal small hsmallMeshPos hsmallMesh hτ hτP N hN hsizeN poly hpoly hmem hrank hRank
    base cells hcells test htest Z hZ
  refine ⟨hmass, ?_⟩
  have hid := allocatedRefinedIdealReference_residue_weighted (τ := τ) (ξ := ξ)
    B U b hR hσ S x jetRows X hMk selection hx modulus q reference residue hb o bW d
    N hW small base cells (physicalCubeEuclideanSample U d poly hmem) (physicalCubeSiteTest test) Z
    δ hcoefficientPeriod hRefined hsize href hresidue
  rw [hid] at he
  exact he

end FixedScale

def AllocatedCommonResidueWeightedOriginalMeshAt (p Psp E e t : ℝ) (δ : ℝ≥0) (A T Kproj Kideal : ℕ) : Prop :=
  ∀ {c : ℝ} (_hc : 0 ≤ c) {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t) (_hR1 : ∀ j, R j ≤ 1)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp c) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp c),
    AllocatedOriginalResidueWeightedMeshAtScale.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim) B U b hR hσ
      (allocatedComparisonDimension m p) Psp E e (allocatedCommonScaleNumeric m p c Psp (E + 4)) δ A T Kproj Kideal

theorem allocatedCommonOriginalMeshAt_residue_weighted
    {p Psp E e t : ℝ} {δ : ℝ≥0} {A T Kproj Kideal : ℕ}
    (horiginal : AllocatedCommonOriginalMeshAt.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B p Psp E e t δ A T Kproj Kideal) :
    AllocatedCommonResidueWeightedOriginalMeshAt.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B p Psp E e t δ A T Kproj Kideal := by
  intro c hc J _ U b R σ hR hσ hσt hR1 hRi hσi
  exact allocatedOriginalPrescribedMeshAtScale_residue_weighted B U b hR hσ
    (horiginal hc U b hR hσ hσt hR1 hRi hσi)

theorem exists_allocated_common_residue_weighted_original_mesh
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {p Psp E : ℝ} (hp : 0 ≤ p) (hPsp : 0 ≤ Psp) (hE : 0 ≤ E)
    (hdim : dim ≤ m + 1) (hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (hpPsp : p ≤ Psp)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    ∃ K : ℕ, 2 ≤ K ∧
      let D := allocatedComparisonDimension m p
      let target := profileReferenceErrorLog Psp (E + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
          (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∃ A₀ T₀ Kproj : ℕ, 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
            AllocatedCommonResidueWeightedOriginalMeshAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim)
              B p Psp E e t δ A₀ T₀ Kproj K := by
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj, horiginal⟩ :=
    exists_allocated_common_original_mesh.{uG,uI,uB,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition
      hp hPsp hE hdim hmPsp hpPsp hvars hI hn
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, A₀, T₀, Kproj, hA₀, hT₀, hKproj,
    allocatedCommonOriginalMeshAt_residue_weighted B horiginal⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uGeom uCover uSpace

theorem exists_uniform_allocated_flexible_original_mesh (m dim : ℕ) :
    ∃ K A₀ T₀ Kproj : ℕ, 2 ≤ K ∧ 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
    (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (_hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (_hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (_hLip : LipschitzWith A ψ) (_hTransition : LipschitzWith T Real.smoothTransition)
    {p Psp E : ℝ} (_hp : 0 ≤ p) (_hPsp : 0 ≤ Psp) (_hE : 0 ≤ E)
    (_hdim : dim ≤ m + 1) (_hmPsp : ((m + 2 : ℕ) : ℝ) ≤ Psp) (_hpPsp : p ≤ Psp)
    (_hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hn : ∀ j, (n j : ℝ) ≤ p),
      let D := allocatedComparisonDimension m p
      let target := profileReferenceErrorLog Psp (E + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (a.1.val + 1))
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (a.1.val + 1)) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (a.1.val + 1)) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
          (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∀ (e' t' : ℝ), e ≤ e' → t' ≤ t →
            AllocatedCommonResidueWeightedOriginalMeshAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim)
              B p Psp E e' t' δ A₀ T₀ Kproj K := by
  obtain ⟨K, hK, hreference⟩ :=
    exists_uniform_allocated_reference_prescribed_flexible.{uG,uI,uB,uGeom,uCover,uSpace} m dim
  obtain ⟨A₀, T₀, Kproj, hA₀, hT₀, hKproj, hfamily⟩ :=
    exists_allocated_ideal_density_source_family.{uSpace,uG,uI,uB,uGeom} m dim
  refine ⟨K, A₀, T₀, Kproj, hK, hA₀, hT₀, hKproj, ?_⟩
  intro G _ _ I _ n B _ ψ hψ hrange hzero hone A T hLip hTransition p Psp E
    hp hPsp hE hdim hmPsp hpPsp hvars hI hn
  let jets := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
  let jetRows := fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim))
  have hdimensions := allocatedComparisonDimensions_of_primitive B jetRows
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) hp hvars hI hn
  have hE4 : 0 ≤ E + 4 := by linarith
  have htarget : 0 ≤ profileReferenceErrorLog Psp (E + 4) := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    unfold profileReferenceErrorLog
    linarith
  have hw : 0 ≤ (m * 2 ^ (m + 1) : ℕ) * Psp := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdimensions.nonneg hPsp hw
  have he := physicalIdealSmoothingLog_nonneg (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    (layerSamplerDegree I n) A T htarget hgain
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    hreference B
      ψ hψ hrange hzero hone A T hLip hTransition hdimensions hPsp hE4
  refine ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_⟩
  intro e' t' hee htt
  have horiginal := allocatedReferencePrescribedIdealAt_original_mesh_of_family B
    hdimensions hPsp hE (he.trans hee) (htt.trans ht1) hK (hcompare e' t' hee htt)
    hT₀ hKproj hfamily
  intro c
  exact allocatedCommonOriginalMeshAt_residue_weighted B
    (allocatedOriginalPrescribedMeshAt_commonScale B hp hPsp hE hdim hmPsp hpPsp hvars horiginal)

end Erdos3.VectorPolynomial

end

end OAI
