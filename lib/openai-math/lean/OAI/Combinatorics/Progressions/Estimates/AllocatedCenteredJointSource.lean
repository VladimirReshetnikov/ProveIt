import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealReferenceTail
import OAI.Combinatorics.Progressions.Geometry.NormalizedSpatialChoiceBudget
import OAI.Combinatorics.Progressions.Probability.JointDensityConstantSubtraction

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

noncomputable def allocatedTupleSpatialError {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (selection : I ↪ J) (N : Type*) [Fintype N] (M period : ℕ)
    (Czero rho xi W delta mesh : ℝ) : ℝ :=
  let gamma := (period : ℝ) ^ Fintype.card (Unit ⊕ I)
  let K := anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * (1 + W)
  let Eone := anisotropicSpatialError selection N M (1 / (M : ℝ)) Czero rho xi + gamma * K * delta
  (n : ℝ) * (Eone + 4 * gamma * K * mesh) *
    (1 + gamma * anisotropicSpatialDensityCap selection (1 / (M : ℝ)) + Eone) ^ n

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

noncomputable def allocatedRefinedTupleDifference : ℂ :=
    let coefficientScale := ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
    let chart := mixedCoveredJetChart U o b hb bW d
    let region := mixedCoveredJetRegion (O := O) (E := Kcov) U o b d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x (fun a => (0 : ℤ) + (x a none : ℤ))
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
    let f := canonicalSpatialSiteDensity selection (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun u r (v : X → (Unit ⊕ (Fin dim)) → ℤ) => ∏ t,
      spatialSiteApprox (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix
            (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u (reference u r))) modulus)))
        modulus f (H t) 4 mesh (v t)
    let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let window := spatialWindow H 4
    let F := fun u r (a : cells) => physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r))) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r))) base
      (boundedColumnResidueRepresentative q a.val) q
    let factor := fun u r (t : cells × window) =>
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ u r t.2.val / (A : ℂ)) * test (F u r t.1 t.2.val)
    let proxy := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r) (fun a => coefficientJetAxisEquiv O I n z.1 a.val) / coefficientScale))
    let source := fun y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides =>
      ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (g y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
    let target := fun u r => ∑ t : cells × window,
      factor u r t * (proxy u r (point (F u r t.1 t.2.val)) : ℂ)
    (whole).complexMean source / (Z : ℂ) -
      ((frozen).complexMean (fun u => ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).complexMean (target u))) /
        (Z : ℂ)

omit [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
  [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedRefinedTupleScalarEstimate_iff {Etail : ℝ} :
    allocatedRefinedTupleScalarEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass point test Cg Z Etail ↔
    ‖allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass point test Z‖ ≤
      Cg * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ) / Z +
      allocatedTupleSpatialError (Fintype.card X) selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus
        C₀ ρ ξ W δ mesh * coarseReferenceMassConstant dim X W S.value / Z + Etail / Z := Iff.rfl

omit [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
  [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedRefinedTupleDifference_exp_bound {E : ℝ}
    (hZ : 1 / 2 ≤ Z)
    (hestimate : allocatedRefinedTupleScalarEstimate B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass point test Cg Z
        (Z * normalizedSpatialShare E))
    (hboundary : Cg * (24 * (probabilityProfileLipschitz : ℝ) *
      Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ) ≤ normalizedSpatialShare E / 2)
    (hspatial : allocatedTupleSpatialError (Fintype.card X) selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus
      C₀ ρ ξ W δ mesh * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare E / 2) :
    ‖allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
      q reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass point test Z‖ ≤ Real.exp (-E) := by
  have hZpos : 0 < Z := by linarith
  have hshare : 0 < normalizedSpatialShare E := Real.exp_pos _
  have hscaled := mul_le_mul_of_nonneg_left hZ hshare.le
  have hfirst : Cg * (24 * (probabilityProfileLipschitz : ℝ) *
      Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ) / Z ≤ normalizedSpatialShare E := by
    apply (div_le_iff₀ hZpos).mpr
    linarith
  have hsecond : allocatedTupleSpatialError (Fintype.card X) selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus
      C₀ ρ ξ W δ mesh * coarseReferenceMassConstant dim X W S.value / Z ≤ normalizedSpatialShare E := by
    apply (div_le_iff₀ hZpos).mpr
    linarith
  have hthird : Z * normalizedSpatialShare E / Z = normalizedSpatialShare E := by field_simp
  have h := (allocatedRefinedTupleScalarEstimate_iff B U b hR hσ S x rows X hM selection hx modulus s hA
    q reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh base cells hmass point test Cg Z).mp hestimate
  rw [hthird] at h
  have hthree : 3 * normalizedSpatialShare E ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp 2 * normalizedSpatialShare E := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hshare.le
      _ = _ := by unfold normalizedSpatialShare; rw [← Real.exp_add]; congr 1; ring
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem allocatedTupleSpatialError_mono_mesh {I J : Type*} [Fintype I] [Fintype J]
    (n : ℕ) (selection : I ↪ J) (N : Type*) [Fintype N] (M period : ℕ)
    {Czero rho xi W delta mesh small : ℝ}
    (hC : 0 ≤ Czero) (hρ : 0 ≤ rho) (hξ : 0 ≤ xi) (hW : 0 ≤ W)
    (hδ : 0 ≤ delta) (hmesh : small ≤ mesh) :
    allocatedTupleSpatialError n selection N M period Czero rho xi W delta small ≤
      allocatedTupleSpatialError n selection N M period Czero rho xi W delta mesh := by
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hE := anisotropicSpatialError_nonneg selection N M hκ hC hρ hξ
  have hcap := anisotropicSpatialDensityCap_nonneg selection hκ
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ
  unfold allocatedTupleSpatialError
  dsimp only
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_left
    · apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left hmesh (by positivity)
    · positivity
  · positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

noncomputable def allocatedProjectedTupleSource : ℂ :=
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let source := fun y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides =>
      ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (g y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
    (whole).complexMean source / (Z : ℂ)

noncomputable def allocatedOriginalTupleSource
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j) : ℂ :=
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let source := fun y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides =>
      ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          (density (affineSampleCoefficientTorus U
            (fun j => translate (fun t => (base t : ℝ)) (poly j))
            (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (poly j) (hmem j))
            (fun k t => (z (k, t) : ℝ))) : ℂ))
    (whole).complexMean source / (Z : ℂ)

noncomputable def allocatedRefinedTupleReference : ℂ :=
    let coefficientScale := ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
    let chart := mixedCoveredJetChart U o b hb bW d
    let region := mixedCoveredJetRegion (O := O) (E := Kcov) U o b d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x (fun a => (0 : ℤ) + (x a none : ℤ))
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
    let f := canonicalSpatialSiteDensity selection (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun u r (v : X → (Unit ⊕ (Fin dim)) → ℤ) => ∏ t,
      spatialSiteApprox (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix
            (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u (reference u r))) modulus)))
        modulus f (H t) 4 mesh (v t)
    let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let window := spatialWindow H 4
    let F := fun u r (a : cells) => physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r))) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r))) base
      (boundedColumnResidueRepresentative q a.val) q
    let factor := fun u r (t : cells × window) =>
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ u r t.2.val / (A : ℂ)) * test (F u r t.1 t.2.val)
    let proxy := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r) (fun a => coefficientJetAxisEquiv O I n z.1 a.val) / coefficientScale))
    let target := fun u r => ∑ t : cells × window,
      factor u r t * (proxy u r (point (F u r t.1 t.2.val)) : ℂ)
    ((frozen).complexMean (fun u => ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).complexMean (target u))) /
        (Z : ℂ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (L₀ : ℕ) (hS : S = selectedLayerSamplerScale B U b R σ hR hσ L₀)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
variable (c : ∀ j, U j)
variable (hc : coefficientConstantCenter U center =
  -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
    (constantCoefficientArray U (fun s => c s.1))))
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "density" => jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hmem center
local notation "hdensity" => jointSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ poly hmem center
local notation "Z" => selectedJointDensityMass bases stride cells widths density
local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "centeredPoly" => (fun j => subtractConstant (Subtype.val (c j)) (poly j))
local notation "centeredMem" => (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hmem j))

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (hZ : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (jointSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ poly hmem center))
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "jointMean" =>
  FiniteProbabilityWeights.complexMean
    (FiniteProbabilityWeights.prod whole
      (selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass density hdensity hZ))
    (fun z => test (physicalCubeRootDifferences
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (Prod.fst z))
      (allocatedPhysicalCubeDirections B U b S x (Prod.fst z))
      (Subtype.val (Prod.fst (Prod.snd z))) (Subtype.val (Prod.snd (Prod.snd z)))))
local notation "source" => (fun a =>
  allocatedOriginalTupleSource B U b hR hσ S x X stride hb o N hN hW hτ hξ a cells hmass
    test Z centeredPoly centeredMem)

include hS hc in
theorem allocatedOriginalTupleSource_centered_jointMean :
    jointMean = 𝔼 a ∈ bases, source a := by
  have hmatch (a : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :=
    allocatedJointDensity_subtractConstant B U b hb o R σ hR hσ L₀ S hS poly hmem center c hc a z
  have hlocal (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S)) :
      (selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass density hdensity hZ).complexMean
        (fun z => test (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) z.1.val z.2.val)) =
        (𝔼 a ∈ bases, ∑' z, ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
          (test (physicalCubeRootDifferences
            (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) a z) * (density a z : ℂ))) / (Z : ℂ) := by
    let f := fun a z => test (physicalCubeRootDifferences
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U b S x y) a z)
    rw [selectedJointFiniteLaw_complexMean bases hbases stride cells widths hwidths hmass
      density hdensity hZ f, FiniteProbabilityWeights.normalizedDensityTest,
      selectedJointReference_densityMass, selectedJointReference,
      FiniteProbabilityWeights.complexMean_prod]
    rw [FiniteProbabilityWeights.uniformFinset_complexMean bases hbases
      (fun a => (selectedResidueFiniteLaw stride cells widths hwidths hmass).complexMean
        (fun z => (density a z.val : ℂ) * f a z.val))]
    congr 1
    apply Finset.expect_congr rfl
    intro a _
    rw [selectedResidueFiniteLaw_complexMean stride cells widths hwidths hmass
      (fun z => (density a z : ℂ) * f a z)]
    apply tsum_congr
    intro z
    change _ * ((density a z : ℂ) * f a z) = _ * (f a z * (density a z : ℂ))
    ring
  rw [FiniteProbabilityWeights.complexMean_prod]
  simp_rw [hlocal]
  rw [FiniteProbabilityWeights.complexMean_div_const, FiniteProbabilityWeights.complexMean_finset_expect]
  simp only [allocatedOriginalTupleSource, hmatch, Finset.expect_eq_sum_div_card,
    Finset.sum_div, div_div, mul_comm]

include hS hc in
theorem allocatedCenteredJointSource_comparison (reference : (X → ℤ) → ℂ) {ε : ℝ}
    (hcomparison : ∀ a ∈ bases, ‖source a - reference a‖ ≤ ε) :
    ‖jointMean - (𝔼 a ∈ bases, reference a)‖ ≤ ε := by
  rw [allocatedOriginalTupleSource_centered_jointMean B U b hR hσ S L₀ hS x X hb o
    poly hmem center c hc N hN hW hτ hξ stride cells bases hbases hmass hZ test,
    ← Finset.expect_sub_distrib]
  exact (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le hbases hcomparison)

end Erdos3.VectorPolynomial

end

end OAI
