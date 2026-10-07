import OAI.Combinatorics.Progressions.Estimates.AllocatedChosenOriginalIdealAt
import OAI.Combinatorics.Progressions.Probability.AllocatedAccuracyReferenceMass

namespace OAI

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

noncomputable def allocatedRefinedSiteReference
    (siteTest : Finset (Fin dim) → (X → ℝ) → ℂ) : ℂ :=
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x (fun a => (0 : ℤ) + (x a none : ℤ))
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
    let f := canonicalSpatialSiteDensity selection (fun a => (0 : ℤ) + (x a none : ℤ))
      (scalarCubeDifferenceMatrix x) hp W S.value hW (Nat.cast_pos.mpr S.positive)
    let pivot := selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection
    let columns := fun u r => Matrix.fromCols
      (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (integerResidueMatrix
        (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u (reference u r))) modulus))
    let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let window := spatialWindow (α := Fin dim) H 4
    let F := allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells
    let proxy := allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d
    let target := fun u r => ∑ t : cells × window,
      (selectedResidueCellWeight q cells V t.1 : ℂ) *
        ((∑ label : X → SpatialSiteLabel (Fin dim) modulus 4 mesh,
          (∏ a, spatialSiteCoefficient pivot (columns u r) modulus f 4 mesh (label a)) *
          ∏ vertex, siteTest vertex (fun a => (physicalCubeVertexValue (F u r t.1 t.2.val) vertex a : ℝ)) *
            physicalResidueSpatialSiteFactor
              (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r)))
              (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r)))
              base (boundedColumnResidueRepresentative q t.1.val) q 4 mesh H label vertex
              (physicalCubeVertexValue (F u r t.1 t.2.val) vertex)) / (A : ℂ)) *
        (proxy u r (point (F u r t.1 t.2.val)) : ℂ)
    (frozen).complexMean (fun u =>
      ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).complexMean (target u)) / (Z : ℂ)

theorem allocatedRefinedTupleReference_site_expansion
    (hq : ∀ t, 0 < q t) (siteTest : Finset (Fin dim) → (X → ℝ) → ℂ) :
    allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
      N hW mesh base cells point (physicalCubeSiteTest siteTest) Z =
    allocatedRefinedSiteReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
      N hW mesh base cells point Z siteTest := by
  classical
  unfold allocatedRefinedTupleReference allocatedRefinedSiteReference
  dsimp only
  apply congrArg (fun z : ℂ => z / (Z : ℂ))
  apply congrArg ((allocatedFrozenTupleWeights (α := Fin dim) B U b S).complexMean)
  funext u
  apply congrArg (((allocatedLongTupleWeights (α := Fin dim) B U b S).fiberLaw
    (principalResidueLabel (residueRefinedPeriod modulus q))).complexMean)
  funext r
  apply Finset.sum_congr rfl
  intro t _
  have he := physicalResidue_spatialSiteExpansion
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r)))
    (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r)))
    base (boundedColumnResidueRepresentative q t.1.val) q hq
    (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (fun _ : X => Matrix.fromCols
      (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (integerResidueMatrix
        (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u (reference u r))) modulus)))
    modulus
    (fun _ : X => canonicalSpatialSiteDensity selection (fun a => (0 : ℤ) + (x a none : ℤ))
      (scalarCubeDifferenceMatrix x)
      (goodScalarKernelTuple_spatial_det_ne_zero selection x (fun a => (0 : ℤ) + (x a none : ℤ))
        (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx)
      W S.value hW (Nat.cast_pos.mpr S.positive))
    (trimmedSpatialRootScale τ N q) 4 mesh t.2.val siteTest
  dsimp only [allocatedRefinedReferenceReconstruction] at *
  rw [← he]
  unfold allocatedRefinedReferenceProfile
  ring

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

include hN hτ in
theorem allocatedRefinedTupleReference_coarse_site_comparison
    (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hroot : ∀ g, |((x g none : ℤ) : ℝ)| ≤ 1 + W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hq : ∀ t, 0 < q t) (hmesh : 0 < mesh) (coarse : ℝ) (hle : mesh ≤ coarse)
    (hZ : 0 < Z) (siteTest : Finset (Fin dim) → (X → ℝ) → ℂ)
    (htest : ∀ vertex u, ‖siteTest vertex u‖ ≤ 1) :
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW mesh base cells point (physicalCubeSiteTest siteTest) Z -
      allocatedRefinedSiteReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW coarse base cells point Z siteTest‖ ≤
      (Fintype.card X * (8 * (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
        (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * coarse) *
        (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X) *
      allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
        B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d N base cells point Z := by
  have hcoarse : 0 < coarse := hmesh.trans_le hle
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ
  have hcap := anisotropicSpatialDensityCap_nonneg selection hκ
  have hvolume : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hs := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hs.1 hs.2 (Nat.cast_pos.mpr S.positive) i
  rw [← allocatedRefinedTupleReference_site_expansion B U b hR hσ S x rows X hM selection hx
    modulus s hA q reference residue hb o bW d N hW coarse base cells point Z hq siteTest]
  apply allocatedRefinedTupleReference_mesh_error B U b hR hσ S x rows X hM selection hx
    modulus s hA q reference residue hb o bW d N hW mesh base cells point
    (physicalCubeSiteTest siteTest) Z coarse _ hvolume hZ
  · positivity
  · exact physicalCubeSiteTest_norm_le siteTest htest
  · intro u r v hv
    have h := allocatedRefinedSpatialKernel_remesh B U b S x X hM selection hx modulus q
      reference N hN hW hτ mesh Q hQ hratio hroot hperiod hq hmesh coarse hcoarse u r v hv
    apply h.trans
    calc
      _ ≤ Fintype.card X * (4 * (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (coarse + coarse)) *
          (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
            anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X := by
        gcongr
      _ = _ := by ring

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

include hN hτ in
theorem allocatedRefinedTupleReference_normalized_coarse_comparison
    {p E : ℝ} (hp : 0 ≤ p) (hm : ((m+1 : ℕ) : ℝ) ≤ p)
    (hdim : ((dim+1 : ℕ) : ℝ) ≤ p) (hG : (Fintype.card G : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p) (hmod : modulus ≤ M^(m+1))
    (hWscale : W = (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hq : ∀ t, 0 < q t) (hZ : 0 < Z)
    (hMass : allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d N base cells point Z ≤
        Real.exp (coefficientErrorVolumeLog p + 4))
    (siteTest : Finset (Fin dim) → (X → ℝ) → ℂ) (htest : ∀ vertex u, ‖siteTest vertex u‖ ≤ 1) :
    let fine := normalizedTupleRadius X selection M p E W / 4
    let coarse := normalizedTupleRadius X selection M p E
      (Fintype.card (LayerSamplerVariables G I n B)) / 4
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW fine base cells point (physicalCubeSiteTest siteTest) Z -
      allocatedRefinedSiteReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW coarse base cells point Z siteTest‖ ≤ normalizedSpatialShare E / 2 := by
  intro fine coarse
  let growth : ℝ := Fintype.card (LayerSamplerVariables G I n B)
  have hgrowth : 0 ≤ growth := Nat.cast_nonneg _
  have hL : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hL0 : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hWge : growth ≤ W := by change W = growth * S.value at hWscale; nlinarith
  have hfine : 0 < fine := (normalizedTupleCoarseMesh_budget X selection M p E hW).1
  have hcoarse := normalizedTupleCoarseMesh_budget X selection M p E hgrowth
  have hle : fine ≤ coarse := normalizedTupleRadius_le_coarse X selection M p E hgrowth hWge
  let Q : ℝ≥0 := ⟨1+growth, by positivity⟩
  have hQ : 1 ≤ Q := by change (1 : ℝ) ≤ 1+growth; linarith
  have hratio : (1+W)/(S.value : ℝ) ≤ Q := by
    change (1+W)/(S.value : ℝ) ≤ 1+growth
    apply (div_le_iff₀ hL0).mpr
    change W = growth * S.value at hWscale
    nlinarith
  have hroot (v : G) : |((x v none : ℤ) : ℝ)| ≤ 1+W := by
    have hcount : 1 ≤ Fintype.card (LayerSamplerVariables G I n B) :=
      Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨Sum.inl v⟩)
    have hc : (1 : ℝ) ≤ growth := by
      change (1 : ℝ) ≤ (Fintype.card (LayerSamplerVariables G I n B) : ℝ)
      exact_mod_cast hcount
    have hbox := Finset.mem_Ico.mp (x v none).property
    have hxbound : |((x v none : ℤ) : ℝ)| ≤ S.value := by
      exact_mod_cast abs_le.mpr ⟨hbox.1, hbox.2.le⟩
    change W = growth * S.value at hWscale
    nlinarith
  have hκ : 0 ≤ 1/(M : ℝ) := by positivity
  have hcap0 := anisotropicSpatialDensityCap_nonneg selection hκ
  have hlip0 := anisotropicSpatialDensityLip_nonneg selection hκ
  let Γ : ℝ := (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim)
  have hΓ0 : 0 ≤ Γ := by positivity
  have hunit : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hdim
  have hperiodB := coefficientErrorPeriod_exp_sq hp hm hMp hmod
  have hΓ : Γ ≤ Real.exp (p^3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hperiodB (sq_nonneg p) _ hunit).trans_eq
      (congrArg Real.exp (by ring))
  have hcap := anisotropicSpatialDensityCap_exp_bound selection hp hM hMp hunit hG
  have hg : Γ * anisotropicSpatialDensityCap selection (1/(M : ℝ)) ≤
      Real.exp (p^3 + anisotropicSpatialCapLog p) := by
    calc
      _ ≤ Real.exp (p^3) * Real.exp (anisotropicSpatialCapLog p) :=
        mul_le_mul hΓ hcap hcap0 (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hk : Γ * (anisotropicSpatialDensityLip selection (1/(M : ℝ)) * (1+growth)) ≤
      Real.exp (p^3) * (anisotropicSpatialDensityLip selection (1/(M : ℝ)) * (1+growth)) :=
    mul_le_mul_of_nonneg_right hΓ (by positivity)
  have hvolume : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hs := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hs.1 hs.2 hL0 i
  have hMass0 := allocatedRefinedReferenceSpatialMass_nonneg (ξ := ξ) B U b hR hσ S x rows X
    modulus s hA q reference residue hb o bW d N base cells point Z hvolume hZ
  have hbudget := hcoarse.2.2 (mul_nonneg hΓ0 hcap0) hg (by positivity) hk hMass0 hMass
  have herr := allocatedRefinedTupleReference_coarse_site_comparison (ξ := ξ) B U b hR hσ S x rows X
    hM selection hx modulus s hA q reference residue hb o bW d N hN hW hτ fine base cells point Z
    Q hQ hratio hroot hperiod hq hfine coarse hle hZ siteTest htest
  apply herr.trans
  change (Fintype.card X * (8 * Γ *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * (1 + growth)) * coarse) *
      (1 + Γ * anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X) *
      allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
        B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d N base cells point Z ≤
    normalizedSpatialShare E / 2
  simpa only [mul_assoc] using hbudget

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel Module Submodule
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (q : X → ℕ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (N : X → ℕ)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (Z : ℝ)

def allocatedRefinedReferenceFunctional (Pc T : ℝ)
    (functional : ((X → (Unit ⊕ Fin dim) → ℤ) → ℂ) → ℂ) : Prop :=
    ∃ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    modulus ≤ M^(m+1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
    ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
    let refined := residueRefinedPeriod modulus q
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*Pc + Fintype.card X*T) ∧
    ∃ hlengths : ∀ t, (Fintype.card (Fin dim)+1)*refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) t,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
          (allocatedPrincipalSides B U b S) →
        (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
        PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
          (allocatedPrincipalSides B U b S))
      (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
          (allocatedPrincipalSides B U b S) →
        (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
        ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) ∧
    ∀ test, functional test = allocatedRefinedTupleReference (τ := τ) (ξ := ξ) B U b hR hσ S x rows X hM selection hx
      modulus s hA q reference residue hb o bW d N hW mesh base cells point test Z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel Module Submodule
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (q : X → ℕ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (N : X → ℕ)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (Z : ℝ)

def allocatedRefinedSiteFunctional (Pc T massBound : ℝ)
    (functional : (Finset (Fin dim) → (X → ℝ) → ℂ) → ℂ) : Prop :=
    ∃ (modulus : ℕ) (hmodulus : 0 < modulus),
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    modulus ≤ M^(m+1) ∧
    (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
    (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
    ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
      (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
    let refined := residueRefinedPeriod modulus q
    (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
    ∃ hRefined : 0 < refined,
    let : NeZero refined := ⟨hRefined.ne'⟩
    (∀ t, q t * modulus ∣ refined) ∧
    (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*Pc + Fintype.card X*T) ∧
    ∃ hlengths : ∀ t, (Fintype.card (Fin dim)+1)*refined ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
        (allocatedPrincipalSides B U b S) t,
    ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
          (allocatedPrincipalSides B U b S) →
        (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
        PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
          (allocatedPrincipalSides B U b S))
      (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
          (allocatedPrincipalSides B U b S) →
        (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
        ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
    (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
    (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) ∧
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d N base cells point Z ≤ massBound ∧
    ∀ test, functional test = allocatedRefinedSiteReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
      N hW mesh base cells point Z test

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_accuracy_coarse_comparison :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (Afourier : ℕ) {P pB E : ℝ} (_hP : 0 ≤ P) (_hpB : 0 ≤ pB) (_hE : 0 ≤ E)
    (_hpP : pB ≤ P) (_hSP : (S.value : ℝ) ≤ Real.exp P)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {Rrank : ℝ}
    (_hτP : 1 / τ ≤ Real.exp (allocatedUnifiedSamplingBudget m dim Afourier P pB E)) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp (allocatedUnifiedSamplingBudget m dim Afourier P pB E))
    (_hsize : ∀ t, Real.exp (((allocatedUnifiedSamplingBudget m dim Afourier P pB E) + K)^K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp (((allocatedUnifiedSamplingBudget m dim Afourier P pB E) + K)^K) ≤ Rrank)
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hdimc : Fintype.card (Fin dim) ≤ m+1) (_hmod : modulus ≤ M ^ (m+1))
    (_hmB : ((m+1 : ℕ) : ℝ) ≤ pB)
    (_hdimB : ((dim+1 : ℕ) : ℝ) ≤ pB)
    (_hvarsB : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pB)
    (_hIB : ∀ j, (Fintype.card (I j) : ℝ) ≤ pB) (_hnB : ∀ j, (n j : ℝ) ≤ pB)
    (_hJB : ∀ j, (Fintype.card (J j) : ℝ) ≤ pB) (_hXB : (Fintype.card X : ℝ) ≤ pB)
    (_hMPB : (M : ℝ) ≤ Real.exp pB) (_hCPB : ∀ j, (C j : ℝ) ≤ Real.exp pB),
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hgi : ∀ y, Integrable (g y) (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))))
    (_hgm : ∀ y, (∫ z, g y z ∂(Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j)))) = 1)
    (_hFourier : allocatedProjectedFourierData B U b S C V d g Afourier P)
    (_hmf : (m : ℝ) ≤ P)
    (_hvarsf : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRif : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσif : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcountf : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (_hIf : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hnf : ∀ j, (n j : ℝ) ≤ P)
    (_hJf : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAPf : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCPf : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVPf : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Pc Tc : ℝ} (_hPc : 0 ≤ Pc) (_hTc : 0 ≤ Tc)
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRP : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc (allocatedCoefficientAccuracyLog m pB (E+3)) Tc) ≤ S.value)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (jetRows j) (s j) (hA j) (1/(M : ℝ)))
    (_hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp Tc)
    {Z : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ 2)
    (_hWscale : W = (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
    (_hspatialPeriod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun v => (0 : ℤ) + (x v none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun v => (0 : ℤ) + (x v none : ℤ)) (scalarCubeDifferenceMatrix x) selection)),
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d N base cells
      (physicalCubeEuclideanSample U d p hm) Z ≤ Real.exp (coefficientErrorVolumeLog pB + 4) ∧
    ∀ (siteTest : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ vertex u, ‖siteTest vertex u‖ ≤ 1) →
    let fine := normalizedTupleRadius X selection M pB E W / 4
    let coarse := normalizedTupleRadius X selection M pB E
      (Fintype.card (LayerSamplerVariables G I n B)) / 4
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW fine base cells (physicalCubeEuclideanSample U d p hm) (physicalCubeSiteTest siteTest) Z -
      allocatedRefinedSiteReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW coarse base cells (physicalCubeEuclideanSample U d p hm) Z siteTest‖ ≤ normalizedSpatialShare E / 2 := by
  obtain ⟨K, hK, hmassBound⟩ := exists_allocated_accuracy_reference_mass_bound m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V
    Afourier P pB E hP hpB hE hpP hSP hC hV ν _ _
    modulus _ hperiod X _ _ q hq reference N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass poly hpoly hm Rrank hτP hstride hsize hrank hRank
    M hM selection hx hdimc hmod hmB hdimB hvarsB hIB hnB hJB hXB hMPB hCPB
    hRefined instRefined s hA residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw
    hgi hgm hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hσ1 Pc Tc hPc hTc hMP hRP hRi hσi hcount hlarge hi hbound Z hZ hZi hWscale hspatialPeriod
  have hD : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp pB :=
    hvarsB.trans (by linarith [Real.add_one_le_exp pB])
  have hMass := hmassBound B U b hR hσ S x hb o bW d C V Afourier hP hpB hE hpP hSP
    hC hV ν modulus hperiod q hq reference N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    base cells hmass poly hpoly hm hτP hstride hsize hrank hRank
    hM selection hx hdimc hmod hdimB hvarsB hIB hnB hJB hXB hMPB hCPB
    hRefined s hA residue hlengths href hr Cinv hCinv hchart hsmall μ g hg hg0 hlaw hgi hgm
    hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hσ1 hPc hTc hMP hRP hRi hσi hcount hlarge hi hbound hZ hZi hD hWscale.le
  refine ⟨hMass, ?_⟩
  intro siteTest htest
  have hG : (Fintype.card G : ℝ) ≤ pB :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvarsB
  exact allocatedRefinedTupleReference_normalized_coarse_comparison B U b hR hσ S x jetRows X
    hM selection hx modulus s hA q reference residue hb o bW d N hN hW hτ base cells
    (physicalCubeEuclideanSample U d poly hm) Z hpB hmB hdimB hG hMPB hmod hWscale
    hspatialPeriod hq hZ hMass siteTest htest

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_normalized_reference_comparison :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (Afourier : ℕ) {P pB E : ℝ} (_hP : 0 ≤ P) (_hpB : 0 ≤ pB) (_hE : 0 ≤ E)
    (_hpP : pB ≤ P) (_hSP : (S.value : ℝ) ≤ Real.exp P)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hdimc : Fintype.card (Fin dim) ≤ m+1) (_hmod : modulus ≤ M ^ (m+1))
    (_hmB : ((m+1 : ℕ) : ℝ) ≤ pB)
    (_hdimB : ((dim+1 : ℕ) : ℝ) ≤ pB)
    (_hvarsB : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pB)
    (_hIB : ∀ j, (Fintype.card (I j) : ℝ) ≤ pB) (_hnB : ∀ j, (n j : ℝ) ≤ pB)
    (_hJB : ∀ j, (Fintype.card (J j) : ℝ) ≤ pB) (_hXB : (Fintype.card X : ℝ) ≤ pB)
    (_hMPB : (M : ℝ) ≤ Real.exp pB) (_hCPB : ∀ j, (C j : ℝ) ≤ Real.exp pB)
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ : ℝ} (hW : 0 ≤ W) (_hτ : 0 < τ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ (normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M pB E) N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {Rrank : ℝ}
    (_hτP : 1 / τ ≤ Real.exp (allocatedUnifiedSamplingBudget m dim Afourier P pB E)) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp (allocatedUnifiedSamplingBudget m dim Afourier P pB E))
    (_hsize : ∀ t, Real.exp (((allocatedUnifiedSamplingBudget m dim Afourier P pB E) + K)^K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp (((allocatedUnifiedSamplingBudget m dim Afourier P pB E) + K)^K) ≤ Rrank),
    ∀ (hRefined : 0 < residueRefinedPeriod modulus q),
    let _ : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
    ∀ (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val+1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hlengths : ∀ t, (Fintype.card (Fin dim)+1)*residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t)
    (_href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (_hr : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u jetRows j v) modulus = residue u r j)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hgi : ∀ y, Integrable (g y) (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))))
    (_hgm : ∀ y, (∫ z, g y z ∂(Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j)))) = 1)
    (_hFourier : allocatedProjectedFourierData B U b S C V d g Afourier P)
    (_hmf : (m : ℝ) ≤ P)
    (_hvarsf : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRif : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσif : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcountf : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (_hIf : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hnf : ∀ j, (n j : ℝ) ≤ P)
    (_hJf : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAPf : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCPf : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVPf : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Pc Tc : ℝ} (_hPc : 0 ≤ Pc) (_hTc : 0 ≤ Tc)
    (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRP : ∀ j, R j ≤ Real.exp Pc)
    (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
    (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc (allocatedCoefficientAccuracyLog m pB (E+3)) Tc) ≤ S.value)
    (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (jetRows j) (s j) (hA j) (1/(M : ℝ)))
    (_hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp Tc)
    {Z : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ 2)
    (_hWscale : W = (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
    (_hspatialPeriod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun v => (0 : ℤ) + (x v none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun v => (0 : ℤ) + (x v none : ℤ)) (scalarCubeDifferenceMatrix x) selection)),
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := (normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M pB E)) (W := W)
      B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d N base cells
      (physicalCubeEuclideanSample U d p hm) Z ≤ Real.exp (coefficientErrorVolumeLog pB + 4) ∧
    ∀ (siteTest : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ vertex u, ‖siteTest vertex u‖ ≤ 1) →
    let fine := normalizedTupleRadius X selection M pB E W / 4
    let coarse := normalizedTupleRadius X selection M pB E
      (Fintype.card (LayerSamplerVariables G I n B)) / 4
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := (normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M pB E))
        B U b hR hσ S x jetRows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW fine base cells (physicalCubeEuclideanSample U d p hm) (physicalCubeSiteTest siteTest) Z -
      allocatedRefinedSiteReference (τ := τ) (ξ := (normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M pB E))
        B U b hR hσ S x jetRows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW coarse base cells (physicalCubeEuclideanSample U d p hm) Z siteTest‖ ≤ normalizedSpatialShare E / 2 := by
  obtain ⟨K, hK, hcompare⟩ := exists_allocated_accuracy_coarse_comparison m dim
  obtain ⟨bside, hbside, hside⟩ := exists_allocatedTupleSideThreshold_bound m
  refine ⟨max K bside, hK.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V
    Afourier P pB E hP hpB hE hpP hSP hC hV ν _ _
    modulus _ hperiod X _ _ q hq
    M hM selection hx hdimc hmod hmB hdimB hvarsB hIB hnB hJB hXB hMPB hCPB
    reference N hN W τ hW hτ base cells hmass poly hpoly hm Rrank hτP hstride hsize hrank hRank
    hRefined instRefined s hA residue hlengths href hr _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw
    hgi hgm hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hσ1 Pc Tc hPc hTc hMP hRP hRi hσi hcount hlarge hi hbound Z hZ hZi hWscale hspatialPeriod
  let Pmass := allocatedUnifiedSamplingBudget m dim Afourier P pB E
  let C₀ := 1 + (S.value : ℝ) + W
  let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
    Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
  let ξ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M pB E
  let ρ := normalizedTupleResolution X (PrincipalTupleIndex B (layerSamplerDegree I n))
    selection M pB E C₀ W cap (allocatedPhysicalEntryBudget B U b S (fun _ => 0))
  obtain ⟨_, _, _, hQ, _, _, hPplus, hpQ, hEQ, _⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim Afourier hP hpB hE
  have hPQ : P ≤ Pmass := by linarith
  have hD : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp pB :=
    hvarsB.trans (by linarith [Real.add_one_le_exp pB])
  have hWQ : W ≤ Real.exp Pmass := by
    calc
      W = (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value := hWscale
      _ ≤ Real.exp pB * Real.exp P := mul_le_mul hD hSP (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (P+pB) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hPplus
  have hG : (Fintype.card G : ℝ) ≤ pB :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvarsB
  have hunit : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ pB := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hdimB
  have hKcut : (Pmass+K)^K ≤ (Pmass+(max K bside : ℕ))^max K bside :=
    shifted_power_self_mono hQ (by omega) (le_max_left _ _)
  have hsideLog := hside B X selection hP hQ hpB hE hPQ hpQ hEQ hvarsB hXB hunit
  have hsideCut := hsideLog.trans
    (shifted_power_self_mono hQ (by omega) (le_max_right K bside))
  obtain ⟨hl, hMassl, hC₀, _hLC, _hWC, hC₀l, hcapl, hentryl, hWl, hprofilel⟩ :=
    allocatedSpatialLateInputBounds B U b S C V hP hPQ hmf hvarsf hR hσ hRif hσif
      hcountf hIf hnf hJf hAPf hSP hCPf hVPf hW hWQ
  have hcap : 0 ≤ cap := by dsimp only [cap]; positivity
  have hentry : 0 ≤ allocatedPhysicalEntryBudget B U b S (fun _ => 0) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0))
  obtain ⟨hξ, hξ1, _, hchoices⟩ := normalizedTupleSpatialChoices
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := X) (m := m)
    selection hM hpB hE hmB hdimB hG hXB hMPB
  obtain ⟨_, _, _, hρ, _, hρ8, hρshift, _, _, _⟩ :=
    hchoices (C₀ := C₀) (W := W) (L := (S.value : ℝ)) (Cg := cap)
      (Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0))
      (by linarith) hW (by exact_mod_cast S.positive) hcap hentry hD hWscale.le
  have hρshift' : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ := by
    simpa only [mul_assoc] using hρshift
  have hspatial (t : X) : 8*(1+W)*(q t : ℝ)*ρ ≤ (ξ*τ)*(N t : ℝ) := by
    exact normalizedTupleSpatialSize X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      hpB hE hl hM hmB hdimB hG hXB hMPB (by linarith) hW hcap hentry
      hC₀l hWl hcapl hentryl hprofilel (Nat.cast_nonneg _)
      ((hstride t).trans (Real.exp_le_exp.mpr hMassl)) hτ
      (by simpa only [one_div] using hτP.trans (Real.exp_le_exp.mpr hMassl))
      ((Real.exp_le_exp.mpr hsideCut).trans (hsize t))
  exact hcompare B U b hR hσ S x hb o bW d C V Afourier hP hpB hE hpP hSP hC hV ν
    modulus hperiod q hq reference N hN hW hτ hξ hξ1 hρ hspatial hρ8 hρshift'
    base cells hmass poly hpoly hm hτP hstride
    (fun t => (Real.exp_le_exp.mpr hKcut).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hKcut).trans hRank)
    hM selection hx hdimc hmod hmB hdimB hvarsB hIB hnB hJB hXB hMPB hCPB
    hRefined s hA residue hlengths href hr Cinv hCinv hchart hsmall μ g hg hg0 hlaw hgi hgm
    hFourier hmf hvarsf hRif hσif hcountf hIf hnf hJf hAPf hCPf hVPf
    hσ1 hPc hTc hMP hRP hRi hσi hcount hlarge hi hbound hZ hZi hWscale hspatialPeriod

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim Afourier : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_chosen_functional_coarsening :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    {pB E T : ℝ} (_hpB : 0 ≤ pB) (_hE : 0 ≤ E) (_hT : 0 ≤ T)
    (_hS : S = allocatedPrimitiveNormalizedScale B U b hR hσ pB E T)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (_hdimc : Fintype.card (Fin dim) ≤ m+1)
    (_hmB : ((m+1 : ℕ) : ℝ) ≤ pB)
    (_hdimB : ((dim+1 : ℕ) : ℝ) ≤ pB)
    (_hvarsB : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pB)
    (_hIB : ∀ j, (Fintype.card (I j) : ℝ) ≤ pB) (_hnB : ∀ j, (n j : ℝ) ≤ pB)
    (_hJB : ∀ j, (Fintype.card (J j) : ℝ) ≤ pB) (_hXB : (Fintype.card X : ℝ) ≤ pB)
    (_hMPB : (M : ℝ) ≤ Real.exp pB) (_hCPB : ∀ j, (C j : ℝ) ≤ Real.exp pB)
    (_hVPB : ∀ j, (V j : ℝ) ≤ Real.exp pB)
    (_hRupB : ∀ j, R j ≤ Real.exp pB) (_hRiB : ∀ j, (R j)⁻¹ ≤ Real.exp pB)
    (_hσiB : ∀ j, (σ j)⁻¹ ≤ Real.exp pB)
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ : ℝ} (hW : 0 ≤ W) (_hτ : 0 < τ)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ (normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M pB E) N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {Rrank : ℝ}
    (_hτp : 1 / τ ≤ Real.exp pB) (_hstrideT : ∀ t, (q t : ℝ) ≤ Real.exp T)
    (_hsize : ∀ t, Real.exp ((pB + E + T + a)^a) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((pB + E + T + a)^a) ≤ Rrank)
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U jets → ℝ)
    (_hg : ∀ y, Continuous (g y)) (_hg0 : ∀ y z, 0 ≤ g y z)
    (_hlaw : ∀ y, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
      (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) jetRows) =
      realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))) (g y))
    (_hgi : ∀ y, Integrable (g y) (Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j))))
    (_hgm : ∀ y, (∫ z, g y z ∂(Measure.pi (fun j => Measure.pi (fun _ : jets j => ν j)))) = 1)
    (_hFourier : allocatedProjectedFourierData B U b S C V d g Afourier (allocatedChosenScaleBudget m pB E T))
    (_hσ1 : ∀ j, σ j ≤ 1)
    {Z : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ 2)
    (_hWscale : W = (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
    (functional : ((X → (Unit ⊕ Fin dim) → ℤ) → ℂ) → ℂ)
    (_hfunctional : allocatedRefinedReferenceFunctional (τ := τ)
      (ξ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M pB E)
      B U b hR hσ S x jetRows X hM selection hx q hb o bW d N hW
      (normalizedTupleRadius X selection M pB E W / 4) base cells
      (physicalCubeEuclideanSample U d p hm) Z (allocatedComparisonDimension m pB) T functional),
    ∃ coarse : (Finset (Fin dim) → (X → ℝ) → ℂ) → ℂ,
      allocatedRefinedSiteFunctional (τ := τ)
        (ξ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M pB E)
        B U b hR hσ S x jetRows X hM selection hx q hb o bW d N hW
        (normalizedTupleRadius X selection M pB E (Fintype.card (LayerSamplerVariables G I n B)) / 4)
        base cells (physicalCubeEuclideanSample U d p hm) Z
        (allocatedComparisonDimension m pB) T (Real.exp (coefficientErrorVolumeLog pB + 4)) coarse ∧
      ∀ siteTest, (∀ vertex u, ‖siteTest vertex u‖ ≤ 1) →
        ‖functional (physicalCubeSiteTest siteTest) - coarse siteTest‖ ≤ normalizedSpatialShare E / 2 := by
  obtain ⟨K, _hK, hcompare⟩ := exists_allocated_normalized_reference_comparison m dim
  obtain ⟨bcut, _hbcut, hcut⟩ := exists_allocatedUnifiedSamplingThreshold_bound m dim Afourier K
  obtain ⟨a, ha, hchosen⟩ := exists_allocatedChosenThreshold_bound m Afourier bcut
  refine ⟨a, ha, ?_⟩
  intro G _ _ I _ instEqI n B _ instEqB J _ U b R σ hR hσ S x _ hb o Q _ bW d _ C V
    pB E T hpB hE hT hS hC hV ν _ _ X _ _ q hq
    M hM selection hx hdimc hmB hdimB hvarsB hIB hnB hJB hXB hMPB hCPB hVPB hRupB hRiB hσiB
    N hN W τ hW hτ base cells hmass poly hpoly hm Rrank hτp hstrideT hsize hrank hRank
    _ _ _ Cinv hCinv hchart hsmall μ _ _ g hg hg0 hlaw hgi hgm hFourier hσ1
    Z hZ hZi hWscale functional hfunctional
  cases Subsingleton.elim instEqI (fun j => Classical.decEq (I j))
  cases Subsingleton.elim instEqB (fun a => Classical.decEq (B a))
  let P := allocatedChosenScaleBudget m pB E T
  let Pc := allocatedComparisonDimension m pB
  let Pmass := allocatedUnifiedSamplingBudget m dim Afourier P pB E
  obtain ⟨hP, hpP, _, hTP, hPcP, hLogP⟩ := allocatedChosenScaleBudget_bounds m hpB hE hT
  obtain ⟨hPc, hpPc, hcountc⟩ := allocatedNormalizedCoefficientInput B hpB hvarsB
  obtain ⟨_, _, _, _, hcountDim, _, _, _, hprofile⟩ := allocatedComparisonDimension_bounds m hpB
  have hSP : (S.value : ℝ) ≤ Real.exp P := by
    rw [hS]
    exact (allocatedPrimitiveNormalizedScale_upper B U b hR hσ hpB hE hT hvarsB hnB hRiB hσiB).trans
      (Real.exp_le_exp.mpr hLogP)
  have hcountf (j : Fin m) :
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P :=
    (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
      (Nat.succ_le_of_lt j.isLt) hpB hvarsB).trans (hcountDim.trans hPcP)
  have hmf : (m : ℝ) ≤ P := by
    have hmB' : (m : ℝ) ≤ pB := by push_cast at hmB; linarith
    exact hmB'.trans hpP
  have hAPf : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P :=
    (probabilityProfileLipschitz_le_comparisonProfileBound.trans (hprofile.trans hPcP)).trans
      (by linarith [Real.add_one_le_exp P])
  obtain ⟨_, _, _, _, _, _, hPplus, hpMass, _, _⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim Afourier hP hpB hE
  have hPMass : P ≤ Pmass := by linarith
  have htotal := (hcut hP hpB hE).trans (hchosen hpB hE hT).2.2
  have hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) jets Pc
      (allocatedCoefficientAccuracyLog m pB (E+3))
      ((m+1 : ℕ)*Pc + Fintype.card X*T)) ≤ S.value := by
    rw [hS]
    exact allocatedPrimitiveNormalizedScale_ready B U b hR hσ jetRows hdimc
      (fun _ => Subtype.val_injective) X hpB hE hT hvarsB hIB hnB hXB
  obtain ⟨modulus, hmodulus, hdata⟩ := hfunctional
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmod, hspatialPeriod, hperiod, s, hA, hi, hRefined, hdata⟩ := hdata
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  obtain ⟨hdiv, hbound, hlengths, reference, residue, href, hr, hfunctionalEq⟩ := hdata
  have hresult := hcompare B U b hR hσ S x hb o bW d C V Afourier hP hpB hE hpP hSP hC hV ν
    modulus hperiod q hq hM selection hx hdimc hmod hmB hdimB hvarsB hIB hnB hJB hXB hMPB hCPB
    reference N hN hW hτ base cells hmass poly hpoly hm
    (hτp.trans (Real.exp_le_exp.mpr hpMass))
    (fun t => (hstrideT t).trans (Real.exp_le_exp.mpr (hTP.trans hPMass)))
    (fun t => (Real.exp_le_exp.mpr htotal).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr htotal).trans hRank)
    hRefined s hA residue hlengths href hr Cinv hCinv hchart hsmall μ g hg hg0 hlaw hgi hgm
    hFourier hmf (hvarsB.trans hpP)
    (fun j => (hRiB j).trans (Real.exp_le_exp.mpr hpP))
    (fun j => (hσiB j).trans (Real.exp_le_exp.mpr hpP)) hcountf
    (fun j => (hIB j).trans hpP) (fun j => (hnB j).trans hpP) (fun j => (hJB j).trans hpP)
    hAPf (fun j => (hCPB j).trans (Real.exp_le_exp.mpr hpP))
    (fun j => (hVPB j).trans (Real.exp_le_exp.mpr hpP)) hσ1 hPc (by positivity)
    (hMPB.trans (Real.exp_le_exp.mpr hpPc))
    (fun j => (hRupB j).trans (Real.exp_le_exp.mpr hpPc))
    (fun j => (hRiB j).trans (Real.exp_le_exp.mpr hpPc))
    (fun j => (hσiB j).trans (Real.exp_le_exp.mpr hpPc)) hcountc hlarge hi hbound hZ hZi hWscale
    (hspatialPeriod (fun v => (0 : ℤ) + (x v none : ℤ)))
  let ξ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M pB E
  let coarseMesh := normalizedTupleRadius X selection M pB E
    (Fintype.card (LayerSamplerVariables G I n B)) / 4
  let coarse := fun siteTest => allocatedRefinedSiteReference (τ := τ) (ξ := ξ)
    B U b hR hσ S x jetRows X hM selection hx modulus s hA q reference residue hb o bW d
    N hW coarseMesh base cells (physicalCubeEuclideanSample U d poly hm) Z siteTest
  refine ⟨coarse, ?_, ?_⟩
  · exact ⟨modulus, hmodulus, hmod, hspatialPeriod, hperiod, s, hA, hi, hRefined,
      hdiv, hbound, hlengths, reference, residue, href, hr, hresult.1, fun _ => rfl⟩
  · intro siteTest htest
    rw [hfunctionalEq (physicalCubeSiteTest siteTest)]
    exact hresult.2 siteTest htest

end Erdos3.VectorPolynomial

end

end OAI
