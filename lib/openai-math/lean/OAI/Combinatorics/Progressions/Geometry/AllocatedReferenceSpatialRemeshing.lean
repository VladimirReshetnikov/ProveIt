import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredJointSource
import OAI.Combinatorics.Progressions.Probability.FiniteSpatialReferenceMass

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped NNReal

theorem canonicalSpatialSiteDensity_lipschitz_ratio {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    {W L κ : ℝ} (hW : 0 ≤ W) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| ≤ 1 + W) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    {Q : ℝ≥0} (hQ : 1 ≤ Q) (hratio : (1 + W) / L ≤ Q) :
    LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ) * Q)
      (canonicalSpatialSiteDensity s root D hp W L hW hL) := by
  have ha : 0 < 1 + W := by linarith
  have h := anisotropicSpatialKernelDensity_bounds root D s ha zero_lt_one hL hκ
    (fun j => by simpa only [mul_one] using hr j) hD hminor
  have hlip : LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ))
      (canonicalSpatialKernelDensity s root D hp W L hW hL) := h.2
  apply coordinateRescaledDensity_lipschitz _ _ hlip
  intro i
  cases i with
  | inl i =>
    change |(1 + W) / (1 + W)| ≤ (Q : ℝ)
    rw [div_self ha.ne', abs_one]
    exact_mod_cast hQ
  | inr i =>
    change |(1 + W) / (L * 1)| ≤ (Q : ℝ)
    rw [mul_one, abs_of_pos (div_pos ha hL)]
    exact hratio

theorem canonicalSpatialSiteDensity_lipschitz_linear_width {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
    (hp : (selectedSpatialPivot root D s).det ≠ 0)
    (n : ℕ) {L κ : ℝ} (hL : 0 < L) (hL1 : 1 ≤ L) (hκ : 0 < κ)
    (hr : ∀ j, |(root j : ℝ)| ≤ 1 + n * L) (hD : ∀ i j, |(D i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    LipschitzWith (Real.toNNReal (anisotropicSpatialDensityLip s κ) * (n + 1))
      (canonicalSpatialSiteDensity s root D hp (n * L) L (by positivity) hL) := by
  apply canonicalSpatialSiteDensity_lipschitz_ratio s root D hp (by positivity) hL hκ hr hD hminor
  · exact le_add_of_nonneg_left zero_le
  · push_cast
    apply (div_le_iff₀ hL).mpr
    nlinarith

end Erdos3

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

noncomputable def allocatedRefinedSpatialKernel :=
    let H := trimmedSpatialRootScale τ N q
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x (fun a => (0 : ℤ) + (x a none : ℤ))
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
    let f := canonicalSpatialSiteDensity selection (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)
    fun u r (v : X → (Unit ⊕ Fin dim) → ℤ) => ∏ t,
      spatialSiteApprox (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix
            (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u (reference u r))) modulus)))
        modulus f (H t) 4 mesh (v t)

noncomputable def allocatedRefinedReferenceReconstruction :=
    fun u r (a : cells) => physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r)))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r))) base
      (boundedColumnResidueRepresentative q a.val) q

noncomputable def allocatedRefinedReferenceProfile :=
    let coefficientScale := ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
    let chart := mixedCoveredJetChart U o b hb bW d
    let region := mixedCoveredJetRegion (O := O) (E := Kcov) U o b d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
    fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r)
          (fun a => coefficientJetAxisEquiv O I n z.1 a.val) / coefficientScale))

noncomputable def allocatedRefinedReferenceSpatialMass : ℝ :=
    let coefficientScale := ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
    let chart := mixedCoveredJetChart U o b hb bW d
    let region := mixedCoveredJetRegion (O := O) (E := Kcov) U o b d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let window := spatialWindow H 4
    let F := fun u r (a : cells) => physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u (reference u r)))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u (reference u r))) base
      (boundedColumnResidueRepresentative q a.val) q
    let proxy := fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r)
          (fun a => coefficientJetAxisEquiv O I n z.1 a.val) / coefficientScale))
    let mass := fun u r => ∑ t : cells × window,
      selectedResidueCellWeight q cells V t.1 * |proxy u r (point (F u r t.1 t.2.val))| / A
    (frozen).mean (fun u => ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).mean (mass u)) / Z

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

omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRefinedReferenceSpatialMass_nonneg
    (hvolume : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)
    (hZ : 0 < Z) :
    0 ≤ allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d N base cells point Z := by
  unfold allocatedRefinedReferenceSpatialMass
  dsimp only
  apply div_nonneg _ hZ.le
  apply FiniteProbabilityWeights.mean_nonneg
  intro u
  apply FiniteProbabilityWeights.mean_nonneg
  intro r
  apply Finset.sum_nonneg
  intro t _
  exact div_nonneg
    (mul_nonneg (selectedResidueCellWeight_nonneg _ _ _ _) (abs_nonneg _)) hvolume.le

theorem allocatedRefinedTupleReference_mesh_error (coarse E : ℝ)
    (hvolume : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)
    (hZ : 0 < Z) (hE : 0 ≤ E) (htest : ∀ v, ‖test v‖ ≤ 1)
    (hspatial : ∀ u r v, v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4 →
      ‖allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW mesh u r v -
        allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW coarse u r v‖ ≤ E) :
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW mesh base cells point test Z -
      allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW coarse base cells point test Z‖ ≤
      E * allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
        B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d N base cells point Z := by
  classical
  let H := trimmedSpatialRootScale τ N q
  let T := trimmedSpatialSlopeScale W τ N q
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
  let index := cells × spatialWindow (α := Fin dim) H 4
  let F := allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells
  let profile := allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d
  let fineKernel := allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW mesh
  let coarseKernel := allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW coarse
  have h := norm_nested_spatial_reference_sub
    (allocatedFrozenTupleWeights (α := Fin dim) B U b S)
    ((allocatedLongTupleWeights (α := Fin dim) B U b S).fiberLaw
      (principalResidueLabel (residueRefinedPeriod modulus q)))
    (fun t : index => selectedResidueCellWeight q cells V t.1)
    (fun u r (t : index) => profile u r (point (F u r t.1 t.2.val)))
    (fun u r (t : index) => fineKernel u r t.2.val)
    (fun u r (t : index) => coarseKernel u r t.2.val)
    (fun u r (t : index) => test (F u r t.1 t.2.val))
    (A := A) hvolume hE hZ
    (fun _ => selectedResidueCellWeight_nonneg _ _ _ _)
    (fun _ _ _ => htest _) (fun u r t => hspatial u r t.2.val t.2.property)
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (q : X → ℕ)

variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (mesh : ℝ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)

include hN hτ in
theorem allocatedRefinedSpatialKernel_remesh (Q : ℝ≥0) (hQ : 1 ≤ Q)
    (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hroot : ∀ g, |((x g none : ℤ) : ℝ)| ≤ 1 + W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hq : ∀ t, 0 < q t) (hmesh : 0 < mesh) (coarse : ℝ) (hcoarse : 0 < coarse) :
    ∀ u r v, v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4 →
      ‖allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW mesh u r v -
        allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW coarse u r v‖ ≤
      Fintype.card X *
        (4 * (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (mesh + coarse)) *
        (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X := by
  intro u r v hv
  let root := fun g => (0 : ℤ) + (x g none : ℤ)
  let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection
  let C := Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)
    (liftResidueMatrix (integerResidueMatrix
      (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u (reference u r))) modulus))
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x root hκ hx
  let f := canonicalSpatialSiteDensity selection root (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  have hL1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hroot' : ∀ g, |(root g : ℝ)| ≤ 1 + W := by
    intro g
    simpa only [root, zero_add] using hroot g
  have hD : ∀ i g, |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value := by
    intro i g
    have hg := Finset.mem_Ico.mp (x g (some i)).property
    change |((x g (some i) : ℤ) : ℝ)| ≤ S.value
    exact_mod_cast abs_le.mpr ⟨hg.1, hg.2.le⟩
  have hminor : 1 / (M : ℝ) ≤
      |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) / (S.value : ℝ))).det| := by
    change 1 / (M : ℝ) ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hf := canonicalSpatialSiteDensity_lipschitz_ratio selection root (scalarCubeDifferenceMatrix x)
    hp hW (Nat.cast_pos.mpr S.positive) hκ hroot' hD hminor hQ hratio
  have hcap := (canonicalSpatialSiteDensity_bounds selection root (scalarCubeDifferenceMatrix x)
    hp hW (Nat.cast_pos.mpr S.positive) hL1 hκ hroot' hD hminor).1
  have hfull : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤ pivotFullImage A C := by
    dsimp only [A, C]
    rw [pivotFullImage_split]
    exact hperiod.trans le_sup_left
  have hi : ((pivotFullImage A C).toAddSubgroup.index : ℝ) ≤
      (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) := by
    exact_mod_cast residueLatticeImage_index_le _ modulus hfull
  have hH : ∀ t, 0 < trimmedSpatialRootScale τ N q t :=
    fun t => (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
  have hv' := (mem_spatialWindow_scaled_iff (trimmedSpatialRootScale τ N q) hH 4 v).mp hv
  have h := vectorSpatialSiteApprox_remesh A (fun _ : X => C) modulus (fun _ => hfull)
    (fun _ => f) (fun _ => hf) (trimmedSpatialRootScale τ N q) (by positivity)
    (anisotropicSpatialDensityCap_nonneg selection hκ.le) (fun _ => hi) (fun _ => hcap)
    (by norm_num : (0 : ℝ) < 4) hmesh hcoarse v hv'
  simpa only [allocatedRefinedSpatialKernel, f, A, C, root, hp, NNReal.coe_mul,
    Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg selection hκ.le)] using h

end Erdos3.VectorPolynomial

end

end OAI
