import OAI.Combinatorics.Progressions.Geometry.AllocatedReferenceSpatialRemeshing

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
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
variable (modulus : ℕ)
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

noncomputable def allocatedRefinedReferenceErrorProfile (η : ℝ) :=
    let coefficientScale := ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
    let chart := mixedCoveredJetChart U o b hb bW d
    let region := mixedCoveredJetRegion (O := O) (E := Kcov) U o b d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
    fun u r => restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u (reference u r) rows Kcov d z.1 z.2 *
        (η / coefficientScale))

noncomputable def allocatedRefinedReferenceErrorWindowMass (η : ℝ) :=
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let F := allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells
    let error := allocatedRefinedReferenceErrorProfile B U b hR hσ S x rows X modulus q reference hb o bW d η
    fun u r => ∑ t : cells × spatialWindow (α := Fin dim) H 4,
      selectedResidueCellWeight q cells V t.1 * error u r (point (F u r t.1 t.2.val)) / A

noncomputable def allocatedRefinedReferenceErrorMass (η : ℝ) : ℝ :=
    (frozen).mean (fun u =>
      ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).mean
        (allocatedRefinedReferenceErrorWindowMass (τ := τ) (ξ := ξ) (W := W)
          B U b hR hσ S x rows X modulus q reference hb o bW d N base cells point η u)) / Z

theorem allocatedRefinedReferenceErrorMass_le (η Etail : ℝ) (hZ : 0 ≤ Z)
    (hbound : ∀ u r, allocatedRefinedReferenceErrorWindowMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus q reference hb o bW d N base cells point η u r ≤ Etail) :
    allocatedRefinedReferenceErrorMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus q reference hb o bW d N base cells point Z η ≤ Etail / Z := by
  unfold allocatedRefinedReferenceErrorMass
  apply div_le_div_of_nonneg_right _ hZ
  calc
    _ ≤ (frozen).mean (fun _ => Etail) := by
      apply FiniteProbabilityWeights.mean_mono
      intro u
      exact (FiniteProbabilityWeights.mean_mono _ (hbound u)).trans_eq
        (FiniteProbabilityWeights.mean_const _ Etail)
    _ = Etail := FiniteProbabilityWeights.mean_const _ Etail

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
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
variable (modulus : ℕ)
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

include hW hτ hξ hN hmass in
theorem allocatedRefinedReferenceSpatialMass_le (η C : ℝ)
    (hRefined : 0 < residueRefinedPeriod modulus q)
    (hlengths : ∀ t, (Fintype.card (Fin dim) + 1) * residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬grid a) sides t)
    (hvolume : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)
    (hZ : 0 < Z) (hg : ∀ y z, 0 ≤ g y z)
    (hcompare : ∀ u r z,
      |(allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).mean
          (fun v => g (principalAxisJoin grid u v) z) -
        allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d u r z| ≤
      allocatedRefinedReferenceErrorProfile B U b hR hσ S x rows X modulus q reference hb o bW d η u r z)
    (hprojected : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 →
      ∀ a : cells,
      (∑ z ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g (principalAxisJoin grid u v) (point
          (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r a z))) ≤
        C * (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
          (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i)) :
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d N base cells point Z ≤
      C / Z + allocatedRefinedReferenceErrorMass (τ := τ) (ξ := ξ) (W := W)
        B U b hR hσ S x rows X modulus q reference hb o bW d N base cells point Z η := by
  let H := trimmedSpatialRootScale τ N q
  let T := trimmedSpatialSlopeScale W τ N q
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
  let index := cells × spatialWindow (α := Fin dim) H 4
  let F := allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells
  let profile := allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d
  let error := allocatedRefinedReferenceErrorProfile B U b hR hσ S x rows X modulus q reference hb o bW d η
  let weights := fun r => allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths
  let localMass := fun u r => ∑ t : index, selectedResidueCellWeight q cells V t.1 *
    |profile u r (point (F u r t.1 t.2.val))| / A
  let localError := fun u r => ∑ t : index, selectedResidueCellWeight q cells V t.1 *
    error u r (point (F u r t.1 t.2.val)) / A
  have hV : ∀ z, 0 < V z := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
  have hlocal (u) (r) : localMass u r ≤ C + localError u r := by
    have hm (v) (hv : (weights r).weight v ≠ 0) :
        (∑ t : index, (selectedResidueCellWeight q cells V t.1 / A) *
          g (principalAxisJoin grid u v) (point (F u r t.1 t.2.val))) ≤ C := by
      apply partition_weighted_mass_le
        (fun a : cells => selectedResidueCellWeight q cells V a)
        (fun a (z : spatialWindow (α := Fin dim) H 4) =>
          g (principalAxisJoin grid u v) (point (F u r a z.val)))
        (fun a => selectedResidueCellWeight_nonneg q cells V a)
        (selectedResidueCellWeight_sum q cells V hV hmass) hvolume
      intro a
      rw [← Finset.sum_subtype (spatialWindow (α := Fin dim) H 4)
        (fun _ => Iff.rfl) (fun z => g (principalAxisJoin grid u v) (point (F u r a z)))]
      exact hprojected u r v hv a
    have h := (weights r).weighted_proxy_abs_mass_le
      (fun t : index => selectedResidueCellWeight q cells V t.1 / A)
      (fun v (t : index) => g (principalAxisJoin grid u v) (point (F u r t.1 t.2.val)))
      (fun t : index => profile u r (point (F u r t.1 t.2.val)))
      (fun t : index => error u r (point (F u r t.1 t.2.val)))
      (fun t => div_nonneg (selectedResidueCellWeight_nonneg q cells V t.1) hvolume.le)
      (fun v t => hg _ _) (fun t => hcompare u r _) hm
    simpa only [localMass, localError, div_mul_eq_mul_div] using h
  let inner := (allocatedLongTupleWeights (α := Fin dim) B U b S).fiberLaw
    (principalResidueLabel (residueRefinedPeriod modulus q))
  have hi (u) : inner.mean (localMass u) ≤ C + inner.mean (localError u) := by
    have h := inner.mean_mono (hlocal u)
    simpa only [inner.mean_add, inner.mean_const] using h
  have ho := (allocatedFrozenTupleWeights (α := Fin dim) B U b S).mean_mono hi
  simp only [FiniteProbabilityWeights.mean_add, FiniteProbabilityWeights.mean_const] at ho
  have h := div_le_div_of_nonneg_right ho hZ.le
  change (allocatedFrozenTupleWeights (α := Fin dim) B U b S).mean
      (fun u => inner.mean (localMass u)) / Z ≤ C / Z +
    (allocatedFrozenTupleWeights (α := Fin dim) B U b S).mean
      (fun u => inner.mean (localError u)) / Z
  simpa only [add_div] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
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
variable (modulus : ℕ)
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

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (hσ1 : ∀ j, σ j ≤ 1) (Cchart : Fin m → ℝ) (hCchart : ∀ j, 0 ≤ Cchart j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cchart j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cchart 1 j)
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hg : ∀ w, Continuous (g w)) (hg0 : ∀ w z, 0 ≤ g w z)
variable (hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
    (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
    (euclideanCoefficientJetMap U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w)
      (allocatedPhysicalCubeDirections B U b S x w) rows) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))

include hW hτ hξ hN hmass hCchart hchart hsmall hg hg0 hlaw in
theorem allocatedRefinedReferenceSpatialMass_of_density (η Etail : ℝ)
    (hq : ∀ t, 0 < q t) (hZ : 0 < Z)
    (hRefined : 0 < residueRefinedPeriod modulus q)
    (hlengths : ∀ t, (Fintype.card (Fin dim) + 1) * residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬grid a) sides t)
    (href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j)
    (hpoint : ∀ u r z,
      |(allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).mean
        (fun v => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a) *
          allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA modulus (residue u r) z| ≤ η)
    (hprojected : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g y (point (physicalResidueReconstruction
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
          (allocatedPhysicalCubeDirections B U b S x y₀) base
          (boundedColumnResidueRepresentative q a) q v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t))
    (htail : ∀ u r, allocatedRefinedReferenceErrorWindowMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus q reference hb o bW d N base cells point η u r ≤ Etail) :
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d N base cells point Z ≤
      (coarseReferenceMassConstant dim X W S.value + Etail) / Z := by
  have hvolume : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hs := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hs.1 hs.2 (Nat.cast_pos.mpr S.positive) i
  have hcompare (u) (r) (z) :
      |(allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).mean
          (fun v => g (principalAxisJoin grid u v) z) -
        allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d u r z| ≤
      allocatedRefinedReferenceErrorProfile B U b hR hσ S x rows X modulus q reference hb o bW d η u r z := by
    exact allocatedPhysicalDensityFamily_refined_comparison B U b hR hσ S x u rows s hA
      hb o hσ1 Cchart hCchart hchart hsmall bW d μ ν
      (fun v => g (principalAxisJoin grid u v))
      (fun v => hg _) (fun v => hg0 _) (fun v => hlaw _)
      (residueRefinedPeriod modulus q) hRefined r hlengths (reference u r) (href u r)
      modulus ⟨∏ t, q t, rfl⟩ hperiod (residue u r) (hresidue u r) (hpoint u r) z
  have hmassBound := allocatedRefinedReferenceSpatialMass_le
    B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d g N hN
    hW hτ hξ base cells hmass point Z η (coarseReferenceMassConstant dim X W S.value)
    hRefined hlengths hvolume hZ hg0 hcompare
    (by
      intro u r v _ a
      have h := hprojected (principalAxisJoin grid u v) (principalAxisJoin grid u (reference u r)) a.val
      rw [physicalSpatial_uniform_volume (trimmedSpatialRootScale τ N q)
        (trimmedSpatialSlopeScale W τ N q) (Nat.cast_ne_zero.mpr S.positive.ne')
        (fun t => trimmedSpatial_scale_ratio hW N q t)] at h
      simpa only [coarseReferenceMassConstant, Fintype.card_fin, mul_assoc,
        allocatedRefinedReferenceReconstruction] using h)
  have he := allocatedRefinedReferenceErrorMass_le B U b hR hσ S x rows X modulus q reference
    hb o bW d N base cells point Z η Etail hZ.le htail
  calc
    _ ≤ coarseReferenceMassConstant dim X W S.value / Z +
        allocatedRefinedReferenceErrorMass (τ := τ) (ξ := ξ) (W := W)
          B U b hR hσ S x rows X modulus q reference hb o bW d N base cells point Z η := hmassBound
    _ ≤ coarseReferenceMassConstant dim X W S.value / Z + Etail / Z := add_le_add le_rfl he
    _ = _ := (add_div _ _ _).symm

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
variable (modulus : ℕ)
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

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (hσ1 : ∀ j, σ j ≤ 1) (Cchart : Fin m → ℝ) (hCchart : ∀ j, 0 ≤ Cchart j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cchart j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cchart 1 j)
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hg : ∀ w, Continuous (g w)) (hg0 : ∀ w z, 0 ≤ g w z)
variable (hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
    (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
    (euclideanCoefficientJetMap U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x w)
      (allocatedPhysicalCubeDirections B U b S x w) rows) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))

include hM hx hσ1 hW hτ hξ hN hmass hCchart hchart hsmall hg hg0 hlaw in
theorem allocatedRefinedReferenceSpatialMass_of_fixed_pivots (η Etail : ℝ)
    (hdim : Fintype.card (Fin dim) ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1)
    {P E T : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hT : 0 ≤ T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O P E T) ≤ S.value)
    (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
    (hbound : (residueRefinedPeriod modulus q : ℝ) ≤ Real.exp T)
    (hq : ∀ t, 0 < q t) (hZ : 0 < Z)
    (hRefined : 0 < residueRefinedPeriod modulus q)
    (hlengths : ∀ t, (Fintype.card (Fin dim) + 1) * residueRefinedPeriod modulus q ≤
      principalAxisLength (fun a => ¬grid a) sides t)
    (href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ u r v,
      (allocatedLongResidueWeights B U b S (residueRefinedPeriod modulus q) hRefined r hlengths).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j)
    (hprojected : ∀ y y₀ (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q),
      (∑ v ∈ spatialWindow (trimmedSpatialRootScale τ N q) 4,
        g y (point (physicalResidueReconstruction
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
          (allocatedPhysicalCubeDirections B U b S x y₀) base
          (boundedColumnResidueRepresentative q a) q v))) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t))
    (htail : ∀ u r, allocatedRefinedReferenceErrorWindowMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus q reference hb o bW d N base cells point η u r ≤ Etail) :
    allocatedRefinedReferenceSpatialMass (τ := τ) (ξ := ξ) (W := W)
      B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d N base cells point Z ≤
      (coarseReferenceMassConstant dim X W S.value + Etail) / Z := by
  classical
  apply allocatedRefinedReferenceSpatialMass_of_density B U b hR hσ S x rows X
    modulus s hA q reference residue hb o bW d g N hN hW hτ hξ base cells hmass point Z
    hσ1 Cchart hCchart hchart hsmall μ ν hg hg0 hlaw η Etail hq hZ
    hRefined hlengths href hperiod hresidue
  · intro u r z
    exact allocatedFixedKernel_refined_pointwise B U b hR hσ S x rows
      hM selection hx hdim hinj hrows hσ1 hP hE hT hη hη1 hMP hRP hRi hσi hcount hηE hlarge
      modulus hperiod s hA hi (residueRefinedPeriod modulus q) hRefined hbound u r hlengths
      (residue u r) (hresidue u r) z
  · exact hprojected
  · exact htail

end Erdos3.VectorPolynomial

end

end OAI
