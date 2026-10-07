import OAI.Combinatorics.Progressions.Estimates.CanonicalSiteBlocks
import OAI.Combinatorics.Progressions.Lattices.AllocatedIdealResidueData
import OAI.Combinatorics.Progressions.Sampling.AllocatedReferenceIdealSampling

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

def AllocatedReferenceActualIdealAt (D Psp E e gainLog t : ℝ) (δ : ℝ≥0) (K : ℕ) : Prop :=
  ∀ (_hmPsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (_hσt : ∀ j, σ j ≤ t)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1)
    (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ)))
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
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    (_hperiodSp : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    [NeZero (residueRefinedPeriod modulus q)]
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
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
    {pNum lengthLog Rrank : ℝ} (_hpNum : 0 ≤ pNum) (_hPspNum : Psp ≤ pNum)
    (_herrorNum : profileReferenceErrorLog Psp E ≤ pNum)
    (_hRP : ∀ j, R j ≤ Real.exp pNum) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pNum)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp pNum)
    (_hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp pNum)
    (_hlengthLog : 0 ≤ lengthLog) (_hlength : (S.value : ℝ) ≤ Real.exp lengthLog)
    (_hmeshLarge : Real.exp (profileReferenceErrorLog Psp E +
      (gainLog + allocatedIdealMeshEnvelope m D pNum e) + 3) ≤ (S.value : ℝ))
    (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVp : ∀ j, (V j : ℝ) ≤ Real.exp pNum)
    (_hX : (Fintype.card X : ℝ) ≤ pNum)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ pNum)
    (_hτP : 1 / τ ≤ Real.exp pNum) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp pNum)
    (spatialMesh : ℝ) (_hspatialMesh : 0 < spatialMesh)
    (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp) (_hperiodM : modulus ≤ Mk ^ (m + 1))
    {Dsp : ℝ} (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (_hDsp : Dsp ≤ Real.exp Psp) (_hWscale : W ≤ Dsp * (S.value : ℝ)),
    let input := allocatedActualProfileInput m D pNum e gainLog lengthLog
    let Pout := allocatedProfileFourierOutput input
    (∀ a, Real.exp ((Pout + K) ^ K) ≤ (N a : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun a => (N a : ℝ)) Rrank (U j) (p j)) →
    Real.exp ((Pout + K) ^ K) ≤ Rrank →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ w, ‖test w‖ ≤ 1) →
    ∀ Z : ℝ, 1 / 2 ≤ Z →
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

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

def AllocatedReferenceChosenIdealAt (D Psp E e t : ℝ) (δ : ℝ≥0) (K : ℕ) : Prop :=
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
    (_hRP : ∀ j, R j ≤ Real.exp pNum) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp pNum)
    (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp pNum),
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1)
    (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1 ↪ B a.val)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (jetRows j) (s j) (hA j) (1 / (Mk : ℝ)))
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
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    (_hperiodSp : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    [NeZero (residueRefinedPeriod modulus q)]
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
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
    (_hX : (Fintype.card X : ℝ) ≤ pNum)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ pNum)
    (_hτP : 1 / τ ≤ Real.exp pNum) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp pNum)
    (spatialMesh : ℝ) (_hspatialMesh : 0 < spatialMesh)
    (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp) (_hperiodM : modulus ≤ Mk ^ (m + 1))
    {Dsp : ℝ} (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (_hDsp : Dsp ≤ Real.exp Psp) (_hWscale : W ≤ Dsp * (S.value : ℝ)),
    let input := allocatedActualProfileInput m D pNum e gainLog lengthLog
    let Pout := allocatedProfileFourierOutput input
    (∀ a, Real.exp ((Pout + K) ^ K) ≤ (N a : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun a => (N a : ℝ)) Rrank (U j) (p j)) →
    Real.exp ((Pout + K) ^ K) ≤ Rrank →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ w, ‖test w‖ ≤ 1) →
    ∀ Z : ℝ, 1 / 2 ≤ Z →
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

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem allocatedIdealMeshEnvelope_mono_smoothing (m : ℕ) {D p e e' : ℝ}
    (hD : 0 ≤ D) (hee : e ≤ e') :
    allocatedIdealMeshEnvelope m D p e ≤ allocatedIdealMeshEnvelope m D p e' := by
  have hi : allocatedIdealLipEnvelope D p e ≤ allocatedIdealLipEnvelope D p e' := by
    unfold allocatedIdealLipEnvelope
    gcongr
  have hg : allocatedIdealGridEnvelope m D p e ≤ allocatedIdealGridEnvelope m D p e' := by
    unfold allocatedIdealGridEnvelope
    linarith
  unfold allocatedIdealMeshEnvelope
  exact add_le_add (mul_le_mul_of_nonneg_left (by linarith) hD) hg

theorem allocatedActualProfileInput_mono_smoothing (m : ℕ) {D p e e' g s : ℝ}
    (hD : 0 ≤ D) (hee : e ≤ e') :
    allocatedActualProfileInput m D p e g s ≤ allocatedActualProfileInput m D p e' g s := by
  unfold allocatedActualProfileInput allocatedIdealLipEnvelope
  gcongr

theorem allocatedProfileFourierInput_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedProfileFourierInput p := by
  have h := allocatedProfileErrorLog_nonneg hp
  unfold allocatedProfileFourierInput
  positivity

theorem allocatedProfileFourierInput_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedProfileFourierInput p ≤ allocatedProfileFourierInput q := by
  unfold allocatedProfileFourierInput allocatedProfileErrorLog allocatedErrorKernelLog
  gcongr

theorem allocatedProfileFourierOutput_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedProfileFourierOutput p := by
  have h := allocatedProfileFourierInput_nonneg hp
  unfold allocatedProfileFourierOutput
  positivity

theorem allocatedProfileFourierOutput_mono {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    allocatedProfileFourierOutput p ≤ allocatedProfileFourierOutput q := by
  have hL := allocatedProfileFourierInput_nonneg hp
  have hLq := allocatedProfileFourierInput_nonneg (hp.trans hpq)
  have hLL := allocatedProfileFourierInput_mono hp hpq
  dsimp only [allocatedProfileFourierOutput]
  gcongr

universe uGeom uCover uSpace

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem AllocatedReferenceActualIdealAt.mono_smoothing
    {D Psp E e e' gainLog t t' : ℝ} {δ : ℝ≥0} {K : ℕ}
    (hD : 0 ≤ D) (he : 0 ≤ e) (hg : 0 ≤ gainLog)
    (hee : e ≤ e') (htt : t' ≤ t)
    (h : AllocatedReferenceActualIdealAt.{_,_,_,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B D Psp E e gainLog t δ K) :
    AllocatedReferenceActualIdealAt.{_,_,_,uGeom,uCover,uSpace}
      (G := G) (dim := dim) B D Psp E e' gainLog t' δ K := by
  intro hmPsp hdimPsp hGPsp J _ U b R σ hR hσ hσt S x Mk hMk selection hx hqDim s hA block hi
    _ hb o Q _ bW d _ C V hC hV ν _ _ modulus _ hperiod hperiodSp X _ _ q hq _ reference residue
    N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget base cells hmass p hp hm
    pNum lengthLog Rrank hpNum hPspNum herrorNum hRP hRi hσi hcount hlengthLog hlength hmeshLarge hCp hVp
    hX hdimNum hτP hstride spatialMesh hspatialMesh hMkPsp hperiodM Dsp hXPsp hDsp hWscale
    input Pout hsize hrank hRank test htest Z hZ
  have hmesh : Real.exp (profileReferenceErrorLog Psp E +
      (gainLog + allocatedIdealMeshEnvelope m D pNum e) + 3) ≤ (S.value : ℝ) := by
    apply le_trans _ hmeshLarge
    apply Real.exp_le_exp.mpr
    linarith [allocatedIdealMeshEnvelope_mono_smoothing m (p := pNum) hD hee]
  have hinput := allocatedActualProfileInput_mono_smoothing m (p := pNum)
    (g := gainLog) (s := lengthLog) hD hee
  have hinput0 := (allocatedActualProfileInput_bounds m hD hpNum he hg hlengthLog).1
  have hout := allocatedProfileFourierOutput_mono hinput0 hinput
  have hout0 := allocatedProfileFourierOutput_nonneg hinput0
  have hthreshold : Real.exp ((allocatedProfileFourierOutput
      (allocatedActualProfileInput m D pNum e gainLog lengthLog) + K) ^ K) ≤
      Real.exp ((Pout + K) ^ K) := by
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add hout le_rfl
  exact h hmPsp hdimPsp hGPsp U b hR hσ (fun j => (hσt j).trans htt)
    S x hMk selection hx hqDim s hA block hi hb o bW d C V hC hV ν modulus hperiod hperiodSp
    q hq reference residue N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget base cells hmass
    p hp hm hpNum hPspNum herrorNum hRP hRi hσi hcount hlengthLog hlength hmesh hCp hVp
    hX hdimNum hτP hstride spatialMesh hspatialMesh hMkPsp hperiodM hXPsp hDsp hWscale
    (fun a => hthreshold.trans (hsize a)) hrank (hthreshold.trans hRank) test htest Z hZ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))
local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_reference_actual_ideal
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
          AllocatedReferenceActualIdealAt (G := G) (dim := dim) B D Psp E e gainLog t δ K := by
  obtain ⟨K, hK, hwindow⟩ := exists_allocated_reference_ideal_sampling m dim
  let target := profileReferenceErrorLog Psp E
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    dsimp [target, profileReferenceErrorLog]
    linarith
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  let gainLog := allocatedProfileGainLog m D Psp w
  have hgainLog : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) hLayer A T target gainLog
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg hLayer A T htarget hgainLog
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcontrol⟩ :=
    exists_allocated_actual_profile_sampling_data (G := G) (α := Fin dim) (O := jets) B
      ψ hψ hrange hzero hone A T hLip hTransition hdim htarget hPsp hw
  refine ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_⟩
  intro hmPsp hdimPsp hGPsp J _ U b R σ hR hσ hσt S x Mk hMk selection hx hqDim s hA block hi
    _ hb o Q _ bW d _ C V hC hV ν _ _ modulus _ hperiod hperiodSp X _ _ q hq _ reference residue
    N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget base cells hmass p hp hm
    pNum lengthLog Rrank hpNum hPspNum herrorNum hRP hRi hσi hcount hlengthLog hlength hmeshLarge hCp hVp
    hX hdimNum hτP hstride spatialMesh hspatialMesh hMkPsp hperiodM Dsp hXPsp hDsp hWscale
    input Pout hsize hrank hRank test htest Z hZ
  let Cm : ℝ≥0 := ⟨(layerKernelIndexBound m Mk : ℝ), Nat.cast_nonneg _⟩
  have hCmw : (Cm : ℝ) ≤ Real.exp w := layerKernelIndexBound_le_exp m hMkPsp
  have hMkNum : (Mk : ℝ) ≤ Real.exp pNum := hMkPsp.trans (Real.exp_le_exp.mpr hPspNum)
  have hgrid := allocatedIdealGridEnvelope_nonneg m hdim.nonneg hpNum he
  have hD : 0 ≤ D := hdim.nonneg
  have hmeshCost : 0 ≤ gainLog + allocatedIdealMeshEnvelope m D pNum e := by
    unfold allocatedIdealMeshEnvelope
    positivity
  have hmesh0 := (physicalIdealErrorShare_pos target (gainLog + allocatedIdealMeshEnvelope m D pNum e)).le
  have hmesh1 := physicalIdealErrorShare_le_one htarget hmeshCost
  have hmesh := physicalIdealErrorShare_scale_mesh (layerTailDegree m) htarget hmeshCost hmeshLarge
  have haccuracy := profileReferenceAccuracy_bounds hPsp hE
  have hδF : (profileReferenceAccuracy Psp E)⁻¹ ≤ Real.exp pNum :=
    haccuracy.2.2.le.trans (Real.exp_le_exp.mpr herrorNum)
  obtain ⟨hPout, hdata⟩ := hcontrol U b hR hσ hσt S x jetRows
    (fun _ => Subtype.val_injective) (fun _ z => z.property) block s hA hMk hi
    hpNum hMkNum hRP hRi hσi hcount hmesh0 hmesh1 hmesh le_rfl hb o bW modulus hperiodM hMkPsp
    Cm hCmw hlengthLog hlength C V hCp hVp hδF
  have haccuracyPout : 1 / profileReferenceAccuracy Psp E ≤ Real.exp Pout := by
    simpa only [one_div] using hδF.trans (Real.exp_le_exp.mpr hPout)
  have hperiodPsp := coefficientErrorPeriod_exp_sq hPsp hmPsp hMkPsp hperiodM
  exact hwindow B U b hR hσ S x hMk selection hx hqDim s hA δ hb o bW d C V hC hV ν
    modulus hperiod hperiodSp q hq reference residue N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    hbudget base cells hmass p hp hm (hpNum.trans hPout) (hX.trans hPout) (hdimNum.trans hPout)
    (hτP.trans (Real.exp_le_exp.mpr hPout)) (fun a => (hstride a).trans (Real.exp_le_exp.mpr hPout))
    haccuracy.1 haccuracyPout hsize hrank hRank spatialMesh hspatialMesh
    haccuracy.1 hPsp hMkPsp hperiodPsp hdimPsp hGPsp hXPsp hDsp hWscale le_rfl le_rfl le_rfl
    hdata test htest Z hZ

end Erdos3.VectorPolynomial

end

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

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

def AllocatedReferenceAtScale (D Psp E e pNum : ℝ) (δ : ℝ≥0) (K : ℕ) : Prop :=
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp E
  let gainLog := allocatedProfileGainLog m D Psp w
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  (S.value : ℝ) ≤ Real.exp lengthLog ∧
  ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1) (_hMkPsp : (Mk : ℝ) ≤ Real.exp Psp)
    (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    ∀ (_hmodulusM : modulus ≤ Mk ^ (m + 1))
      (_hspatial : ∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection))
      (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range),
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
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))

theorem allocatedReferenceActualIdealAt_chooseScale
    {D Psp E e t : ℝ} {δ : ℝ≥0} {K : ℕ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e)
    (hcompare : AllocatedReferenceActualIdealAt.{_, _, _, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e
      (allocatedProfileGainLog m D Psp ((m * 2 ^ (m + 1) : ℕ) * Psp)) t δ K) :
    AllocatedReferenceChosenIdealAt.{_, _, _, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t δ K := by
  intro hmPsp hdimPsp hGPsp J _ U b R σ hR hσ hσt pNum hPspNum hcount herrorNum hRP hRi hσi
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp E
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  have hpNum : 0 ≤ pNum := hPsp.trans hPspNum
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hdim.nonneg hPsp hE
  obtain ⟨_, hQ, _, _, _, hQL⟩ := allocatedIdealScaleInput_bounds m hdim.nonneg hpNum he hw herror
  have hlengthLog : 0 ≤ lengthLog := hQ.trans hQL
  have hlength : (S.value : ℝ) ≤ Real.exp lengthLog :=
    allocatedIdealScale_upper B U b hR hσ hdim hpNum he hw herror hRi hσi
  have hmesh : Real.exp (profileReferenceErrorLog Psp E +
      (allocatedProfileGainLog m D Psp w + allocatedIdealMeshEnvelope m D pNum e) + 3) ≤
      (S.value : ℝ) :=
    (Real.exp_le_exp.mpr (allocatedReferenceIdealLength_mesh m hdim.nonneg hPsp hE hpNum)).trans
      (allocatedIdealScale_lower B U b hR hσ D pNum e w error)
  refine ⟨hlength, ?_⟩
  intro x Mk hMk selection hx hqDim s hA block hi _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod hperiodSp X _ _ q hq _ reference residue N hN W τ ξ ρ hW hτ hξ hξ1 hρ
    hsizeSp hρ8 hρshift hbudget base cells hmass p hp hm Rrank hCp hVp hX hdimNum hτP hstride
    spatialMesh hspatialMesh hMkPsp hperiodM Dsp hXPsp hDsp hWscale input Pout hsize hrank hRank test htest Z hZ
  exact hcompare hmPsp hdimPsp hGPsp U b hR hσ hσt S x hMk selection hx hqDim s hA block hi
    hb o bW d C V hC hV ν modulus hperiod hperiodSp q hq reference residue N hN hW hτ hξ hξ1 hρ
    hsizeSp hρ8 hρshift hbudget base cells hmass p hp hm hpNum hPspNum herrorNum hRP hRi hσi
    hcount hlengthLog hlength hmesh hCp hVp hX hdimNum hτP hstride spatialMesh hspatialMesh
    hMkPsp hperiodM hXPsp hDsp hWscale hsize hrank hRank test htest Z hZ

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
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

def AllocatedReferencePrescribedIdealAt (D Psp E e t : ℝ) (δ : ℝ≥0) (K : ℕ) : Prop :=
  ∀ (_hmPsp : ((m + 1 : ℕ) : ℝ) ≤ Psp) (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp)
    (_hGPsp : (Fintype.card G : ℝ) ≤ Psp)
    {J : Fin m → Type uGeom} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
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
  AllocatedReferenceAtScale.{uG,uI,uB,uGeom,uCover,uSpace}
    (G := G) (dim := dim) B U b hR hσ D Psp E e pNum δ K

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

theorem allocatedReferenceChosenIdealAt_prescribeData
    {D Psp E e t : ℝ} {δ : ℝ≥0} {K Ktail : ℕ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e)
    (hK : 2 ≤ K) (hKtail : 2 ≤ Ktail)
    (htail : AllocatedIdealReferenceTailAt.{uG, uI, uB, uGeom, uCover, uSpace} m dim Ktail)
    (hcompare : AllocatedReferenceChosenIdealAt.{_, _, _, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t δ K) :
    AllocatedReferencePrescribedIdealAt.{_, _, _, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp E e t δ (max K Ktail) := by
  have hD := hdimensions.nonneg
  intro hmPsp hdimPsp hGPsp J _ U b R σ hR hσ hσt pNum hPspNum hcount
    herrorNum hRefineNum hRP hRi hσi
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  let error := allocatedReferenceIdealError m D Psp E
  let S := allocatedIdealScale (G := G) B U b hR hσ D pNum e w error
  obtain ⟨hS, hcomparison⟩ := hcompare hmPsp hdimPsp hGPsp U b hR hσ hσt
    hPspNum hcount herrorNum hRP hRi hσi
  refine ⟨hS, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp modulus hmodulus
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  intro _ hmodulusM hspatial hperiod
  obtain ⟨s, hA, hi⟩ := goodKernel_fixed_pivots S.positive selection
    (one_div_pos.mpr (Nat.cast_pos.mpr hMk)) x hx
    (fun j : Fin m => j.val + 1) jetRows
    (fun _ => Subtype.val_injective) (fun _ z => z.property)
  refine ⟨s, hA, hi, ?_⟩
  intro block _ hb o Q _ bW d _ C V hC hV ν _ _ X _ _ hXPsp q hq hqPsp
  let refined := residueRefinedPeriod modulus q
  have hRefined : 0 < refined := residueRefinedPeriod_pos hmodulus q hq
  let : NeZero refined := ⟨hRefined.ne'⟩
  have hp : 0 ≤ pNum := hPsp.trans hPspNum
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hD hPsp hE
  have hsize := allocatedIdealScale_refined_window_size (G := G) (dim := dim)
    B U b hR hσ hD hp he hw herror
    hPsp hRefineNum hmodulusM hMkPsp hXPsp q hqPsp
  have hmodulusP : (modulus : ℝ) ≤ Real.exp ((m + 1 : ℕ) * Psp) := by
    calc
      _ ≤ (Mk : ℝ) ^ (m + 1) := by exact_mod_cast hmodulusM
      _ ≤ (Real.exp Psp) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hMkPsp _
      _ = _ := (Real.exp_nat_mul Psp (m + 1)).symm
  have hdiv : modulus ∣ refined := ⟨∏ a, q a, rfl⟩
  obtain ⟨reference, residue, href, hr⟩ :=
    allocated_refined_residue_data B U b S x jetRows hRefined hdiv hsize
  have hP2 : Psp * Psp ≤ pNum := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (m + 1)) hPsp]
  have hstride : (Fintype.card X : ℝ) * Psp ≤ pNum :=
    (mul_le_mul_of_nonneg_right hXPsp hPsp).trans hP2
  have hbound := residueRefinedPeriod_exp_bound modulus q hmodulusP hqPsp
  have hboundNum : (refined : ℝ) ≤
      Real.exp ((m + 1 : ℕ) * pNum + Fintype.card X * Psp) := by
    apply hbound.trans
    apply Real.exp_le_exp.mpr
    gcongr
  have hpoint : ∀ (hσ1 : ∀ j, σ j ≤ 1) u r (z : AllocatedLongJetRows B U b S jets),
      |(allocatedLongResidueWeights B U b S refined hRefined r hsize).mean
          (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := jets) a) *
            allocatedLongJetDensity B U b hR hσ S x u v jetRows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u jetRows s hA modulus (residue u r) z| ≤
          physicalIdealErrorShare error (allocatedIdealVolumeEnvelope m D pNum) := by
    intro hσ1 u r
    exact allocatedIdealScale_refined_pointwise (D := D) (p := pNum) (e := e) (w := w) (E := error)
      B U b hR hσ hdimensions hp he hw herror hcount hRP hRi hσi x jetRows hMk
      (hMkPsp.trans (Real.exp_le_exp.mpr hPspNum)) selection hx
      (by simpa only [Fintype.card_fin] using hqDim)
      (fun _ => Subtype.val_injective) (fun _ z => z.property) hσ1 hPsp hstride
      modulus hperiod s hA hi refined hRefined hboundNum u r hsize (residue u r) (hr u r)
  refine ⟨hRefined, stride_mul_dvd_residueRefinedPeriod modulus q,
    hbound, hsize, reference, residue, href, hr, hpoint, ?_, ?_⟩
  · exact allocatedFixedData_source_of_pointwise B U b hR hσ S x jetRows X hMk selection hx
      modulus s hA q reference residue hb o bW d hRefined hsize href hperiod (hspatial _) hr hpoint
  intro N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget base cells hmass
    poly hpoly hmem Rrank hCp hVp hτP spatialMesh hspatialMesh Dsp hDsp hWscale
  have hdimX := (mul_le_mul hdimPsp hXPsp (Nat.cast_nonneg (Fintype.card X)) hPsp).trans hP2
  have hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ pNum := by
    simpa only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hdimX
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let gainLog := allocatedProfileGainLog m D Psp w
  let input := allocatedActualProfileInput m D pNum e gainLog lengthLog
  let Pout := allocatedProfileFourierOutput input
  obtain ⟨_, hQ, _, _, _, hQL⟩ := allocatedIdealScaleInput_bounds m hD hp he hw herror
  have hs : 0 ≤ lengthLog := hQ.trans hQL
  have hgain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hD hPsp hw
  have hinput : 0 ≤ input := (allocatedActualProfileInput_bounds m hD hp he hgain hs).1
  have hPout : 0 ≤ Pout := by
    have hlog := allocatedProfileErrorLog_nonneg hinput
    dsimp only [Pout, allocatedProfileFourierOutput, allocatedProfileFourierInput]
    positivity
  intro _input _Pout hsizeN hrank hRankN test htest Z hZ
  have hold : Real.exp ((Pout + K) ^ K) ≤ Real.exp ((Pout + (max K Ktail : ℕ)) ^ max K Ktail) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hPout (Nat.le_trans (by decide) hK) (le_max_left _ _))
  have hnew : Real.exp ((Pout + Ktail) ^ Ktail) ≤ Real.exp ((Pout + (max K Ktail : ℕ)) ^ max K Ktail) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hPout (Nat.le_trans (by decide) hKtail) (le_max_right _ _))
  constructor
  · exact htail (G := G) (I := I) (n := n) (J := J) (Q := Q) (X := X) (M := Mk)
      (R := R) (σ := σ) (D := D) (Psp := Psp) (pNum := pNum) (E := E) (e := e)
      (w := w) (lengthLog := lengthLog) (Rrank := Rrank) (W := W) (τ := τ) (ξ := ξ)
      (ρ := ρ) (mesh := spatialMesh) (Dsp := Dsp)
      B U b hR hσ S x hb o bW d C V hC hV ν hMk selection hx modulus
      (hspatial _) hperiod q hq reference N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget
      hspatialMesh base cells hmass poly hpoly hmem test htest hdimensions hPsp hp hE he hw hs
      hmPsp hdimPsp hGPsp hXPsp (hXPsp.trans hPspNum) hdim hCp hVp hτP
      (fun a => (hqPsp a).trans (Real.exp_le_exp.mpr hPspNum)) herrorNum hmodulusM hMkPsp hS
      hDsp hWscale (fun a => hnew.trans (hsizeN a)) hrank (hnew.trans hRankN) Z hZ
  exact hcomparison x hMk selection hx hqDim s hA block hi hb o bW d C V hC hV ν
    modulus hperiod (hspatial _) q hq reference residue N hN hW hτ hξ hξ1 hρ
    hsizeSp hρ8 hρshift hbudget base cells hmass poly hpoly hmem hCp hVp
    (hXPsp.trans hPspNum) hdim hτP
    (fun a => (hqPsp a).trans (Real.exp_le_exp.mpr hPspNum))
    spatialMesh hspatialMesh hMkPsp hmodulusM hXPsp hDsp hWscale
    (fun a => hold.trans (hsizeN a)) hrank (hold.trans hRankN) test htest Z hZ

end Erdos3.VectorPolynomial

end

end OAI
