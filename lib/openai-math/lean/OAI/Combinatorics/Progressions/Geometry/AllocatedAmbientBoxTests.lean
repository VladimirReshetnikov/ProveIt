/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedBufferedSiteTwist
import OAI.Combinatorics.Progressions.Estimates.FiniteWindowVolumeCancellation
import OAI.Combinatorics.Progressions.Lattices.AllocatedNormalizedProductResidueCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)

local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)

noncomputable def allocatedRecenteredSpatialTwist (r : labels)
    (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
    (t : terms) (s : Finset (Fin dim)) (u : X → ℤ) : ℂ :=
  physicalResidueSpatialSiteFactor
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r))
    (allocatedPhysicalCubeDirections B U b S x (wholeReference r)) base
    (boundedColumnResidueRepresentative q a) q 4 mesh (trimmedSpatialRootScale τ N q) t s u

omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecenteredSpatialTwist_bound (hmesh : 0 < mesh)
    (r : labels) (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
    (t : terms) (s : Finset (Fin dim)) (u : X → ℤ) :
    ‖allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base r a t s u‖ ≤ 1 := by
  exact physicalResidueSpatialSiteFactor_bound _ _ base _ q 4 hmesh _ t s u

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W : ℝ} (hW : 0 ≤ W)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))

local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

theorem allocatedRecenteredResidueWeight_expansion (hq : ∀ z, 0 < q z)
    (r : labels) (a : cells) (v : X → (Unit ⊕ Fin dim) → ℤ)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) :
    allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
        N hW mesh base cells (physicalCubeSiteTest test) r a v =
      ∑ t : terms, (coeff (principalResidueLabel modulus (wholeReference r)) t / ((volume : ℝ) : ℂ)) *
        ∏ s, test s (fun z => (physicalCubeVertexValue (reconstruct r a.val v) s z : ℝ)) *
          twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s) := by
  have hexp :
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus (wholeReference r)) v *
        physicalCubeSiteTest test (reconstruct r a.val v) =
      ∑ t : terms, coeff (principalResidueLabel modulus (wholeReference r)) t *
        ∏ s, test s (fun z => (physicalCubeVertexValue (reconstruct r a.val v) s z : ℝ)) *
          twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s) := by
    exact physicalResidue_spatialSiteExpansion _ _ base _ q hq _ _ modulus _ _ 4 mesh v test
  unfold allocatedRecenteredResidueWeight
  rw [div_mul_eq_mul_div, hexp, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem allocatedRecenteredSpatialCoefficient_sum_le
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection)) (r : labels) :
    (∑ t : terms, ‖coeff (principalResidueLabel modulus (wholeReference r)) t / ((volume : ℝ) : ℂ)‖) ≤
      allocatedSpatialCoefficientCap X selection M modulus mesh / volume := by
  have hscales (z : X) : 0 < trimmedSpatialRootScale τ N q z ∧
      0 < trimmedSpatialSlopeScale W τ N q z := trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)
  have hA : 0 < volume := Finset.prod_pos (fun z _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales z).1 (hscales z).2 (Nat.cast_pos.mpr S.positive) i))
  simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg hA.le, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (allocatedSpatialExpansionCoefficient_sum_le B U b S x X hM selection hx modulus hW mesh
      hbudget hperiod (principalResidueLabel modulus (wholeReference r))) hA.le

theorem allocatedRecenteredSpatial_sum_expansion (hq : ∀ z, 0 < q z)
    (r : labels) (a : cells) (vset : Finset (X → (Unit ⊕ Fin dim) → ℤ))
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (F : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) :
    (∑ v ∈ vset, allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x
        hM selection hx N hW mesh base cells (physicalCubeSiteTest test) r a v * F v) =
      ∑ t : terms, (coeff (principalResidueLabel modulus (wholeReference r)) t / ((volume : ℝ) : ℂ)) *
        ∑ v ∈ vset, (∏ s, test s (fun z => (physicalCubeVertexValue (reconstruct r a.val v) s z : ℝ)) *
          twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s)) * F v := by
  simp_rw [allocatedRecenteredResidueWeight_expansion B U b S X modulus q wholeReference x N mesh base
    hM selection hx hW cells hq, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem allocatedRecenteredSpatial_mixedMass_le [NeZero (residueRefinedPeriod modulus q)]
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (law : FiniteProbabilityWeights labels)
    {T : labels → Type*} [∀ r, Fintype (T r)] (c : ∀ r, T r → ℂ) :
    law.mean (fun r => ∑ t : terms, ∑ k : T r,
      ‖(coeff (principalResidueLabel modulus (wholeReference r)) t / ((volume : ℝ) : ℂ)) * c r k‖) ≤
      (allocatedSpatialCoefficientCap X selection M modulus mesh / volume) *
        law.mean (fun r => ∑ k, ‖c r k‖) := by
  have hpoint (r : labels) : (∑ t : terms, ∑ k : T r,
        ‖(coeff (principalResidueLabel modulus (wholeReference r)) t / ((volume : ℝ) : ℂ)) * c r k‖) ≤
      (allocatedSpatialCoefficientCap X selection M modulus mesh / volume) * ∑ k, ‖c r k‖ := by
    simp only [norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (allocatedRecenteredSpatialCoefficient_sum_le B U b S X modulus q wholeReference x N mesh
        hM selection hx hW hq hN hτ hbudget hperiod r) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  exact (law.mean_mono hpoint).trans_eq (law.mean_const_mul _ _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRecenteredClippedFullGridCover_expansion
    (hq : ∀ z, 0 < q z) (hmesh : 0 < mesh)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (htest : ∀ s u, ‖test s u‖ ≤ 1)
    (hg : ∀ k s u, ‖g r k s u‖ ≤ 1) :
    let factor := fun (t : terms) (k : ∀ j, ((coverWitness r).expansion j).Term)
        (s : Finset (Fin dim)) (u : X → ℤ) =>
      test s (fun z => (u z : ℝ)) * twist r.val a.val t s u *
        g r k s (fun j => (((eval (fun z => (u z : ℝ)) (p j.1) j.2) /
          commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle))
    (∀ t k s u, ‖factor t k s u‖ ≤ 1) ∧
    ∀ v : X → (Unit ⊕ Fin dim) → ℤ,
      allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells (physicalCubeSiteTest test) r.val a v *
        allocatedClippedFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
          (point v) r.val =
      ∑ t : terms, ∑ k : ∀ j, ((coverWitness r).expansion j).Term,
        ((coeff (principalResidueLabel modulus (wholeReference r.val)) t / ((volume : ℝ) : ℂ)) *
          coverSiteCoefficient (coverWitness r).expansion k) *
        (allocatedClippedFullGridGlobalPrefactor B U b S rowSets d
            (allocatedIdealCoverSupport (G := G) B rowSets) x hb o bW refined (coverWitness r).representative
            (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
            (physicalCubeRowSample U d rows p hm (point v)) *
          ∏ s, factor t k s (physicalCubeVertexValue (point v) s)) := by
  dsimp only
  constructor
  · intro t k s u
    rw [norm_mul, norm_mul]
    have ht := allocatedRecenteredSpatialTwist_bound (τ := τ) B U b S X modulus q wholeReference x N mesh base
      hmesh r.val a.val t s u
    exact (mul_le_mul (mul_le_mul (htest s _) ht (norm_nonneg _) zero_le_one)
      (hg k s _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by norm_num)
  · intro v
    rw [allocatedRecenteredResidueWeight_expansion B U b S X modulus q wholeReference x N mesh base
      hM selection hx hW cells hq]
    simp only [allocatedClippedFullGridCoverValue, dite_eq_left r.property]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.prod_mul_distrib]
    ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRecenteredProductFullGridCover_expansion
    (hq : ∀ z, 0 < q z) (hmesh : 0 < mesh)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (htest : ∀ s u, ‖test s u‖ ≤ 1)
    (hg : ∀ k s u, ‖g r k s u‖ ≤ 1) :
    let factor := fun (t : terms) (k : ∀ j, ((coverWitness r).expansion j).Term)
        (s : Finset (Fin dim)) (u : X → ℤ) =>
      test s (fun z => (u z : ℝ)) * twist r.val a.val t s u *
        g r k s (fun j => (((eval (fun z => (u z : ℝ)) (p j.1) j.2) /
          commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle))
    (∀ t k s u, ‖factor t k s u‖ ≤ 1) ∧
    ∀ v : X → (Unit ⊕ Fin dim) → ℤ,
      allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells (physicalCubeSiteTest test) r.val a v *
        allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
          (point v) r.val =
      ∑ t : terms, ∑ k : ∀ j, ((coverWitness r).expansion j).Term,
        ((coeff (principalResidueLabel modulus (wholeReference r.val)) t / ((volume : ℝ) : ℂ)) *
          coverSiteCoefficient (coverWitness r).expansion k) *
        (allocatedProductFullGridPrefactor B U b S rowSets d
            (allocatedProductIdealSiteRadius (G := G) B rowSets) (allocatedProductIdealSiteRadius_pos B rowSets) x hb o bW refined (coverWitness r).representative
            (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
            (physicalCubeRowSample U d rows p hm (point v)) *
          ∏ s, factor t k s (physicalCubeVertexValue (point v) s)) := by
  dsimp only
  constructor
  · intro t k s u
    rw [norm_mul, norm_mul]
    have ht := allocatedRecenteredSpatialTwist_bound (τ := τ) B U b S X modulus q wholeReference x N mesh base
      hmesh r.val a.val t s u
    exact (mul_le_mul (mul_le_mul (htest s _) ht (norm_nonneg _) zero_le_one)
      (hg k s _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by norm_num)
  · intro v
    rw [allocatedRecenteredResidueWeight_expansion B U b S X modulus q wholeReference x N mesh base
      hM selection hx hW cells hq]
    simp only [allocatedProductFullGridCoverValue, dite_eq_left r.property]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.prod_mul_distrib]
    ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)

local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W ξ : ℝ} (hW : 0 ≤ W)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))

local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4
local notation "V" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

theorem allocatedRecentered_exists_twisted_source
    (hq : ∀ z, 0 < q z) (hmesh : 0 < mesh)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells V z)
    (r : labels) (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (F : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hcoeff : allocatedSpatialCoefficientCap X selection M modulus mesh ≤ C)
    (hsource : δ ≤ ‖∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window, allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x
        hM selection hx N hW mesh base cells (physicalCubeSiteTest test) r a v * F (reconstruct r a.val v)‖) :
    ∃ (a : cells) (t : terms),
      coeff (principalResidueLabel modulus (wholeReference r)) t ≠ 0 ∧
      (∀ s u, ‖twist r a.val t s u‖ ≤ 1) ∧
      δ / C ≤ ‖(∑ v ∈ window,
        (∏ s, test s (fun z => (physicalCubeVertexValue (reconstruct r a.val v) s z : ℝ)) *
          twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s)) *
            F (reconstruct r a.val v)) / ((volume : ℝ) : ℂ)‖ := by
  let c : cells → ℂ := fun a => (selectedResidueCellWeight q cells V a : ℂ)
  let d : terms → ℂ := coeff (principalResidueLabel modulus (wholeReference r))
  let z : cells → terms → ℂ := fun a t => (∑ v ∈ window,
    (∏ s, test s (fun u => (physicalCubeVertexValue (reconstruct r a.val v) s u : ℝ)) *
      twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s)) *
        F (reconstruct r a.val v)) / ((volume : ℝ) : ℂ)
  have hc : (∑ a, ‖c a‖) ≤ 1 := by
    simp only [c, Complex.norm_real, Real.norm_of_nonneg (selectedResidueCellWeight_nonneg q cells V _)]
    exact (selectedResidueCellWeight_sum q cells V hV hZ).le
  have hd : (∑ t, ‖d t‖) ≤ C :=
    (allocatedSpatialExpansionCoefficient_sum_le B U b S x X hM selection hx modulus hW mesh
      hbudget hperiod _).trans hcoeff
  have heq (a : cells) :
      (∑ v ∈ window, allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x
        hM selection hx N hW mesh base cells (physicalCubeSiteTest test) r a v * F (reconstruct r a.val v)) =
        ∑ t, d t * z a t := by
    rw [allocatedRecenteredSpatial_sum_expansion B U b S X modulus q wholeReference x N mesh base
      hM selection hx hW cells hq r a window test (fun v => F (reconstruct r a.val v))]
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [d, z]
    ring
  simp_rw [heq, Finset.mul_sum, ← mul_assoc] at hsource
  obtain ⟨a, t, _, hdt, ht⟩ := exists_large_weighted_pair_nonzero c (fun _ => d) z hδ zero_lt_one hC hc
    (fun _ => hd) hsource
  refine ⟨a, t, hdt, ?_, ?_⟩
  · exact allocatedRecenteredSpatialTwist_bound B U b S X modulus q wholeReference x N mesh base hmesh r a.val t
  · simpa only [one_mul] using ht

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRecenteredMaskedSpatialAssembly
    (hq : ∀ z, 0 < q z) (hmesh : 0 < mesh)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hg : ∀ k s u, ‖g r k s u‖ ≤ 1) (hfI : ∀ k s z, ‖fI k s z‖ ≤ 1)
    (error : ℝ)
    (herr : ∀ y : EuclideanJetLayers U (fun j : Fin m =>
        {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)}),
      ‖allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
          refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
        allocatedProductChartIdealApproximation B U b S rowSets x (coverWitness r).representative
          refined d period radius positiveRadius hb o bW cI fI y‖ ≤ error) :
    let c := fun t : terms × (∀ j, ((coverWitness r).expansion j).Term) =>
      (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
        coverSiteCoefficient (coverWitness r).expansion t.2
    let Ψ := fun (t : terms × (∀ j, ((coverWitness r).expansion j).Term)) (label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)))) k s (u : X → ℤ) =>
      twist r.val a.val t.1 s u * (fun k s (u : X → ℤ) => g r k s (fun j => (((eval (fun z => (u z : ℝ)) (p j.1) j.2) / commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle))) t.2 s u * (fun label k s (u : X → ℤ) => allocatedMaskedSiteChartFactor B U b S o hb bW d radius positiveRadius period (label s) (fI k s) (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ)))) label k s u
    (∀ t label k s u, ‖Ψ t label k s u‖ ≤ 1) ∧
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      ∀ v : X → (Unit ⊕ Fin dim) → ℤ,
        ‖allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r.val a v *
            allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
              (point v) r.val -
          ∑ t : terms × (∀ j, ((coverWitness r).expansion j).Term), ∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))), ∑ k,
            (c t * (allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative refined d period cI) label k) * ∏ s,
              test s (fun z => (physicalCubeVertexValue (point v) s z : ℝ)) *
                Ψ t label k s (physicalCubeVertexValue (point v) s)‖ ≤
          (∑ t, ‖c t‖) * error := by
  intro c Ψ
  constructor
  · intro t label k s u
    dsimp only [Ψ]
    rw [norm_mul, norm_mul]
    have ht := allocatedRecenteredSpatialTwist_bound (τ := τ) B U b S X modulus q wholeReference
      x N mesh base hmesh r.val a.val t.1 s u
    have hi := allocatedMaskedSiteChartFactor_norm B U b S o hb bW d radius positiveRadius period
      (label s) (fI k s) (hfI k s) (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ)))
    exact (mul_le_mul (mul_le_mul ht (hg t.2 s _) (norm_nonneg _) zero_le_one)
      hi (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by norm_num)
  · intro test htest v
    have hprevious := allocatedRecenteredProductFullGridCover_expansion (τ := τ) B U b hR S X modulus q
      wholeReference coverWitness hb o bW d g δ x hM selection hx N hW mesh base cells p hm r a
      hq hmesh test htest hg
    have hphysical := allocatedProductPrefactor_physical_site_error B U b S x
      (coverWitness r).representative refined d period radius positiveRadius hb o bW cI fI
      p hp hm (point v) hR δ error herr
    have hsub := finiteSitePrefactor_substitution_error c (allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative refined d period cI)
      (fun (t : terms × (∀ j, ((coverWitness r).expansion j).Term)) s u => test s (fun z => (u z : ℝ)) *
        twist r.val a.val t.1 s u * (fun k s (u : X → ℤ) => g r k s (fun j => (((eval (fun z => (u z : ℝ)) (p j.1) j.2) / commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle))) t.2 s u)
      (fun label k s (u : X → ℤ) => allocatedMaskedSiteChartFactor B U b S o hb bW d radius positiveRadius period (label s) (fI k s) (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ)))) (physicalCubeVertexValue (point v))
      (allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
        refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
          (physicalCubeRowSample U d rows p hm (point v)))
      (fun t s u => hprevious.1 t.1 t.2 s u) hphysical
    rw [hprevious.2 v]
    simpa only [c, Ψ, Fintype.sum_prod_type, mul_assoc] using hsub

omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRecenteredMaskedSpatialAssembly_coefficient_mass :
    (∑ t : terms × (∀ j, ((coverWitness r).expansion j).Term), ∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))), ∑ k,
      ‖((coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
        coverSiteCoefficient (coverWitness r).expansion t.2) * (allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative refined d period cI) label k‖) =
      (∑ t : terms, ‖coeff (principalResidueLabel modulus (wholeReference r.val)) t / ((volume : ℝ) : ℂ)‖) *
        (∑ k : (∀ j, ((coverWitness r).expansion j).Term), ‖coverSiteCoefficient (coverWitness r).expansion k‖) *
        ∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))), ∑ k, ‖(allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative refined d period cI) label k‖ := by
  rw [finiteSitePrefactor_coefficient_mass]
  simp only [Fintype.sum_prod_type, norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRecenteredMaskedSpatialAssembly_pointwise
    (hq : ∀ z, 0 < q z) (hmesh : 0 < mesh)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hg : ∀ k s u, ‖g r k s u‖ ≤ 1) (hfI : ∀ k s z, ‖fI k s z‖ ≤ 1)
    (error : EuclideanJetLayers U (fun j : Fin m =>
      {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)}) → ℝ)
    (herr : ∀ y : EuclideanJetLayers U (fun j : Fin m =>
        {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)}),
      ‖allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
          refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
        allocatedProductChartIdealApproximation B U b S rowSets x (coverWitness r).representative
          refined d period radius positiveRadius hb o bW cI fI y‖ ≤ error y) :
    let c := fun t : terms × (∀ j, ((coverWitness r).expansion j).Term) =>
      (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
        coverSiteCoefficient (coverWitness r).expansion t.2
    let Ψ := fun (t : terms × (∀ j, ((coverWitness r).expansion j).Term)) (label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)))) k s (u : X → ℤ) =>
      twist r.val a.val t.1 s u * (fun k s (u : X → ℤ) => g r k s (fun j => (((eval (fun z => (u z : ℝ)) (p j.1) j.2) / commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle))) t.2 s u * (fun label k s (u : X → ℤ) => allocatedMaskedSiteChartFactor B U b S o hb bW d radius positiveRadius period (label s) (fI k s) (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ)))) label k s u
    (∀ t label k s u, ‖Ψ t label k s u‖ ≤ 1) ∧
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      ∀ v : X → (Unit ⊕ Fin dim) → ℤ,
        ‖allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r.val a v *
            allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
              (point v) r.val -
          ∑ t : terms × (∀ j, ((coverWitness r).expansion j).Term), ∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))), ∑ k,
            (c t * (allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative refined d period cI) label k) * ∏ s,
              test s (fun z => (physicalCubeVertexValue (point v) s z : ℝ)) *
                Ψ t label k s (physicalCubeVertexValue (point v) s)‖ ≤
          (∑ t, ‖c t‖) * error (physicalCubeRowSample U d rows p hm (point v)) := by
  intro c Ψ
  constructor
  · intro t label k s u
    dsimp only [Ψ]
    rw [norm_mul, norm_mul]
    have ht := allocatedRecenteredSpatialTwist_bound (τ := τ) B U b S X modulus q wholeReference
      x N mesh base hmesh r.val a.val t.1 s u
    have hi := allocatedMaskedSiteChartFactor_norm B U b S o hb bW d radius positiveRadius period
      (label s) (fI k s) (hfI k s) (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ)))
    exact (mul_le_mul (mul_le_mul ht (hg t.2 s _) (norm_nonneg _) zero_le_one)
      hi (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)).trans_eq (by norm_num)
  · intro test htest v
    have hprevious := allocatedRecenteredProductFullGridCover_expansion (τ := τ) B U b hR S X modulus q
      wholeReference coverWitness hb o bW d g δ x hM selection hx N hW mesh base cells p hm r a
      hq hmesh test htest hg
    have hphysical := herr (physicalCubeRowSample U d rows p hm (point v))
    rw [allocatedProductChartIdealApproximation_physical B U b S x
      (coverWitness r).representative refined d period radius positiveRadius hb o bW cI fI
      p hp hm (point v)] at hphysical
    have hsub := finiteSitePrefactor_substitution_error c (allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative refined d period cI)
      (fun (t : terms × (∀ j, ((coverWitness r).expansion j).Term)) s u => test s (fun z => (u z : ℝ)) *
        twist r.val a.val t.1 s u * (fun k s (u : X → ℤ) => g r k s (fun j => (((eval (fun z => (u z : ℝ)) (p j.1) j.2) / commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle))) t.2 s u)
      (fun label k s (u : X → ℤ) => allocatedMaskedSiteChartFactor B U b S o hb bW d radius positiveRadius period (label s) (fI k s) (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ)))) (physicalCubeVertexValue (point v))
      (allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
        refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ)
          (physicalCubeRowSample U d rows p hm (point v)))
      (fun t s u => hprevious.1 t.1 t.2 s u) hphysical
    rw [hprevious.2 v]
    simpa only [c, Ψ, Fintype.sum_prod_type, mul_assoc] using hsub

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

noncomputable def allocatedRecenteredMaskedSpatialApproximation
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (v : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
    let c := fun t : terms × (∀ j, ((coverWitness r).expansion j).Term) =>
      (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
        coverSiteCoefficient (coverWitness r).expansion t.2
    let Ψ := fun (t : terms × (∀ j, ((coverWitness r).expansion j).Term)) (label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)))) k s (u : X → ℤ) =>
      twist r.val a.val t.1 s u * (fun k s (u : X → ℤ) => g r k s (fun j => (((eval (fun z => (u z : ℝ)) (p j.1) j.2) / commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle))) t.2 s u * (fun label k s (u : X → ℤ) => allocatedMaskedSiteChartFactor B U b S o hb bW d radius positiveRadius period (label s) (fI k s) (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ)))) label k s u
          ∑ t : terms × (∀ j, ((coverWitness r).expansion j).Term), ∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))), ∑ k,
            (c t * (allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative refined d period cI) label k) * ∏ s,
              test s (fun z => (physicalCubeVertexValue (point v) s z : ℝ)) *
                Ψ t label k s (physicalCubeVertexValue (point v) s)

local notation "H" => trimmedSpatialRootScale τ N q
local notation "factor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X)
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d radius positiveRadius
local notation "gridMass" => ∑ k, ‖coverSiteCoefficient (AllocatedFullGridResidueWitness.expansion (coverWitness r)) k‖
local notation "spatialCap" => allocatedSpatialCoefficientCap X selection M modulus mesh

omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRecenteredMaskedSpatialApproximation_window_error
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ) (hmesh : 0 < mesh)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hg : ∀ k s u, ‖g r k s u‖ ≤ 1) (hfI : ∀ k s z, ‖fI k s z‖ ≤ 1)
    (hrows : ∀ z, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H z)
    (hscale : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H z)
    {T A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (href : ∀ cell : ColumnResiduePattern (Option (Fin dim)) X q,
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight q {cell} (referenceJetEnvelopeWidths q H) z,
        selectedResidueDensityMass q {cell} (referenceJetEnvelopeWidths q H)
          (fun z => amp * ‖cutoff (physicalCubeRowSample U d rows p hm
            (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ T)
    (herr : ∀ y : EuclideanJetLayers U (fun j : Fin m =>
        {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)}),
      ‖allocatedProductFullGridPrefactor B U b S rowSets d radius positiveRadius x hb o bW
          refined (coverWitness r).representative (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
        allocatedProductChartIdealApproximation B U b S rowSets x (coverWitness r).representative
          refined d period radius positiveRadius hb o bW cI fI y‖ ≤ amp * A * (‖cutoff y‖ * ε)) :
    ∀ (test : Finset (Fin dim) → (X → ℝ) → ℂ), (∀ s u, ‖test s u‖ ≤ 1) →
      (∑ v ∈ spatialWindow H 4,
        ‖allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
            N hW mesh base cells (physicalCubeSiteTest test) r.val a v *
            allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
              (point v) r.val -
          allocatedRecenteredMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
            coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period cI fI test v‖) ≤
        (spatialCap * gridMass) * (A * ε) * (factor * T) := by
  intro test htest
  let c := fun t : terms × (∀ j, ((coverWitness r).expansion j).Term) =>
    (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
      coverSiteCoefficient (coverWitness r).expansion t.2
  have hpos (z : X) := trimmedSpatial_scales_pos hW hτ N q z (hN z) (hq z)
  have hvolume : 0 < volume := Finset.prod_pos (fun z _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hpos z).1 (hpos z).2 (Nat.cast_pos.mpr S.positive) i))
  have hcap := allocatedRecenteredSpatialCoefficient_sum_le (τ := τ) B U b S X modulus q
    wholeReference x N mesh hM selection hx hW hq hN hτ hbudget hperiod r.val
  have hc : (∑ t, ‖c t‖) ≤ (spatialCap * gridMass) / volume := by
    calc
      _ = (∑ t : terms, ‖coeff (principalResidueLabel modulus (wholeReference r.val)) t /
          ((volume : ℝ) : ℂ)‖) * gridMass := by
        simp only [c, Fintype.sum_prod_type, norm_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ (spatialCap / volume) * gridMass :=
        mul_le_mul_of_nonneg_right hcap (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      _ = _ := by ring
  have hmass := allocatedNormalizedCutoff_reconstructed_cell_mass B U b S rowSets o hb bW d
    radius positiveRadius p hm q N hq hN modulus wholeReference x base hW hτ hrows hscale href r.val a.val
  have hpoint := allocatedRecenteredMaskedSpatialAssembly_pointwise (τ := τ) B U b hR S X modulus q
    wholeReference coverWitness hb o bW d g δ x hM selection hx N hW mesh base cells p hm r a
    period cI fI hq hmesh hp hg hfI (fun y => amp * A * (‖cutoff y‖ * ε)) herr
  apply finiteWindow_norm_sum_cancel_volume (spatialWindow H 4)
    (fun v => allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
      N hW mesh base cells (physicalCubeSiteTest test) r.val a v *
      allocatedProductFullGridCoverValue B U b hR S refined coverWitness hb o bW d g δ x p hm
        (point v) r.val -
      allocatedRecenteredMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
        coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period cI fI test v)
    (fun v => amp * ‖cutoff (physicalCubeRowSample U d rows p hm (point v))‖)
    hvolume (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (mul_nonneg hA hε)
    (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc hmass
  intro v _
  apply (hpoint.2 test htest v).trans_eq
  dsimp only [c]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ≥0) (base : X → ℤ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
variable (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
variable (period : ℕ)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "expansion" => AllocatedFullGridResidueWitness.expansion (coverWitness r)
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r.val)
local notation "directions" => allocatedPhysicalCubeDirections B U b S x (wholeReference r.val)
local notation "residue" => boundedColumnResidueRepresentative q a

variable (spatial : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
variable (kg : ∀ i, ((coverWitness r).expansion i).Term)
variable (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))
variable (fi : (LayerSamplerAxis I n → ℝ) → ℂ) (s : Finset (Fin dim))

noncomputable def allocatedRecenteredNormalizedSiteFactor
    (gridLabel : ∀ i, ZMod (((coverWitness r).expansion i).period (kg i))) (u : X → ℤ) : ℂ :=
  restrictedComplexChartDensity (mixedCoveredJetChart (O := fun _ => Unit) U o b hb bW d)
    (mixedCoveredJetRegion U o b d (fun j (_ : Unit) => standardLatticeSmallBox (J j))) 1
    (allocatedNormalizedCommonSiteFactor B U b S expansion ig radius positiveRadius kg s fi d
      root directions base residue q 4 mesh (trimmedSpatialRootScale τ N q) (fun z => (N z : ℝ)) spatial
      (siteTwistCommonModulus_spatial_dvd modulus q expansion kg period)
      (siteTwistCommonModulus_grid_dvd modulus q expansion kg period)
      (siteTwistCommonModulus_ideal_dvd modulus q expansion kg period) label gridLabel u)
    (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ)))

variable [∀ i, NeZero (((coverWitness r).expansion i).period (kg i))]

omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecenteredNormalizedSiteFactor_sum
    (g : (((Σ j, J j) → UnitAddCircle) → ℂ))
    (hsite : ∀ (u₀ : ∀ j, euclideanSubspace (U j)) (w₀ : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
      (∀ j, (QuotientAddGroup.mk (u₀ j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w₀ j))) →
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w₀ j)) i| ≤ 1 / 4) →
      g (fun v => ((((u₀ v.1).val v.2) / commonSitePeriod expansion kg : ℝ) : UnitAddCircle)) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) expansion ig kg s
          (fun i => ((w₀ (ig i).1).2 (ig i).2 : ZMod (((coverWitness r).expansion i).period (kg i))))
          (allocatedFullMixedSiteValue (R := R) U b w₀) / 2)
    (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j)
    (hN : ∀ z, 0 < N z) (u : X → ℤ) :
    (allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base
        r.val a spatial s u *
      g (fun v => (((eval (fun z => (u z : ℝ)) (p v.1) v.2) / commonSitePeriod expansion kg : ℝ) : UnitAddCircle))) *
      allocatedMaskedSiteChartFactor B U b S o hb bW d radius positiveRadius period label fi
        (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ))) =
      ∑ gridLabel : ∀ i, ZMod (((coverWitness r).expansion i).period (kg i)),
        allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
          hb o bW d x N mesh base p hm r a period spatial kg label fi s gridLabel u := by
  exact allocatedPhysicalSiteTwist_common_global B U b S expansion ig radius positiveRadius kg s fi
    o hb bW d p hm root directions base residue q 4 mesh (trimmedSpatialRootScale τ N q)
    (fun z => (N z : ℝ)) spatial
    (siteTwistCommonModulus_spatial_dvd modulus q expansion kg period)
    (siteTwistCommonModulus_grid_dvd modulus q expansion kg period)
    (siteTwistCommonModulus_ideal_dvd modulus q expansion kg period) label hR C hC hchart
    (allocatedProductGridRadius_source_budget B rowSets C hC (fun j => (hR j).le) hsmall)
    g hsite (fun z => Nat.cast_ne_zero.mpr (hN z).ne') u

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

variable [∀ (i : {i // allocatedGridAxis (I := I) U b S.value i})
  (ki : ((coverWitness r).expansion i).Term), NeZero (((coverWitness r).expansion i).period ki)]

noncomputable def allocatedRecenteredNormalizedSpatialApproximation
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (v : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
    let c := fun t : terms × (∀ j, ((coverWitness r).expansion j).Term) =>
      (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
        coverSiteCoefficient (coverWitness r).expansion t.2
    ∑ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
      ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)),
        ∑ k : K,
          ∑ gridLabel : Finset (Fin dim) → ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i)),
            (c t * allocatedProductMaskedIdealCoefficient B U b S rowSets x
              (coverWitness r).representative refined d period cI label k) *
              ∏ s, test s (fun z => (physicalCubeVertexValue (point v) s z : ℝ)) *
                allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
                  hb o bW d x N mesh base p hm r a.val period t.1 t.2 (label s) (fI k s) s
                  (gridLabel s) (physicalCubeVertexValue (point v) s)

local notation "ig" => allocatedGridIntegerAxis B U b S

include hR in
omit [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedRecenteredMaskedSpatialApproximation_normalized
    (hsite : ∀ kg s (u₀ : ∀ j, euclideanSubspace (U j)) (w₀ : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
      (∀ j, (QuotientAddGroup.mk (u₀ j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w₀ j))) →
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w₀ j)) i| ≤ 1 / 4) →
      g r kg s (fun v => ((((u₀ v.1).val v.2) / commonSitePeriod (coverWitness r).expansion kg : ℝ) : UnitAddCircle)) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) (coverWitness r).expansion ig kg s
          (fun i => ((w₀ (ig i).1).2 (ig i).2 : ZMod (((coverWitness r).expansion i).period (kg i))))
          (allocatedFullMixedSiteValue (R := R) U b w₀) / 2)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j)
    (hN : ∀ z, 0 < N z)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedRecenteredMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
      coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period cI fI test v =
    allocatedRecenteredNormalizedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
      coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI test v := by
  unfold allocatedRecenteredMaskedSpatialApproximation allocatedRecenteredNormalizedSpatialApproximation
  dsimp only
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (s : Finset (Fin dim))
    (gl : ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i))) =>
      test s (fun z => (physicalCubeVertexValue (point v) s z : ℝ)) *
        allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
          hb o bW d x N mesh base p hm r a.val period t.1 t.2 (label s) (fI k s) s gl
          (physicalCubeVertexValue (point v) s))]
  apply congrArg (fun z : ℂ =>
    ((coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
      coverSiteCoefficient (coverWitness r).expansion t.2 *
      allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative
        refined d period cI label k) * z)
  apply Finset.prod_congr rfl
  intro s _
  rw [← Finset.mul_sum]
  apply congrArg (fun z : ℂ =>
    test s (fun z => (physicalCubeVertexValue (point v) s z : ℝ)) * z)
  exact allocatedRecenteredNormalizedSiteFactor_sum (τ := τ) B U b S X modulus q wholeReference coverWitness
    hb o bW d x N mesh base p hm r a.val period t.1 t.2 (label s) (fI k s) s
    (g r t.2 s) (hsite t.2 s) hR C hC hchart hsmall hN (physicalCubeVertexValue (point v) s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ≥0) (base : X → ℤ)
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
variable (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
variable (period : ℕ)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "expansion" => AllocatedFullGridResidueWitness.expansion (coverWitness r)
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r.val)
local notation "directions" => allocatedPhysicalCubeDirections B U b S x (wholeReference r.val)
local notation "residue" => boundedColumnResidueRepresentative q a

variable (spatial : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
variable (kg : ∀ i, ((coverWitness r).expansion i).Term)
variable (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))
variable (fi : (LayerSamplerAxis I n → ℝ) → ℂ) (s : Finset (Fin dim))

omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecenteredNormalizedSiteFactor_norm
    (hR : ∀ j, 0 < R j)
    {T Vg Cg Hg : {i // allocatedGridAxis (I := I) U b S.value i} → ℝ} {L LI : ℝ≥0}
    (he : ∀ i, ((coverWitness r).expansion i).Bounds (T i) (Vg i) (Cg i) L (Hg i))
    (Q : ℝ≥0) (hQ : ∀ i, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig i).1 (ig i).2) : ℝ) + 1) ≤ Q)
    (hf : ∀ y, ‖fi y‖ ≤ 1)
    (hI : LipschitzWith LI (bufferedCoordinateProjection
      (allocatedGridAxis (I := I) U b S.value) radius positiveRadius fi))
    (hmesh : 0 < mesh) (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ)
    (gridLabel : ∀ i, ZMod (((coverWitness r).expansion i).period (kg i))) (u : X → ℤ) :
    ‖allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
      hb o bW d x N mesh base p hm r a period spatial kg label fi s gridLabel u‖ ≤ 1 := by
  let Lsp : ℝ≥0 := ⟨8 / τ, div_nonneg (by norm_num) hτ.le⟩
  have hscale (z : X) : |(N z : ℝ) / ((q z : ℝ) * trimmedSpatialRootScale τ N q z)| ≤ Lsp := by
    rw [trimmedSpatialRootScale_normalized_ratio N q hτ hN hq z]
    exact (abs_of_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hτ.le)).le
  unfold allocatedRecenteredNormalizedSiteFactor
  apply restrictedComplexChartDensity_norm_le _ _
    (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Set.Subset.rfl)) _ zero_le_one
  intro w
  exact allocatedNormalizedCommonSiteFactor_norm B U b S expansion ig radius positiveRadius kg s fi d
    root directions base residue q 4 mesh (trimmedSpatialRootScale τ N q) (fun z => (N z : ℝ)) spatial
    (siteTwistCommonModulus_spatial_dvd modulus q expansion kg period)
    (siteTwistCommonModulus_grid_dvd modulus q expansion kg period)
    (siteTwistCommonModulus_ideal_dvd modulus q expansion kg period) label hR he Q hQ hf hI hmesh hscale
    gridLabel u w

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

variable [∀ (i : {i // allocatedGridAxis (I := I) U b S.value i})
  (ki : ((coverWitness r).expansion i).Term), NeZero (((coverWitness r).expansion i).period ki)]

noncomputable def allocatedAmbientMaskedSpatialApproximation
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (u : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
    let c := fun t : terms × (∀ j, ((coverWitness r).expansion j).Term) =>
      (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
        coverSiteCoefficient (coverWitness r).expansion t.2
    let Ψ := fun (t : terms × (∀ j, ((coverWitness r).expansion j).Term)) (label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)))) k s (u : X → ℤ) =>
      twist r.val a.val t.1 s u * (fun k s (u : X → ℤ) => g r k s (fun j => (((eval (fun z => (u z : ℝ)) (p j.1) j.2) / commonSitePeriod (coverWitness r).expansion k : ℝ) : UnitAddCircle))) t.2 s u * (fun label k s (u : X → ℤ) => allocatedMaskedSiteChartFactor B U b S o hb bW d radius positiveRadius period (label s) (fI k s) (physicalSingleSiteValue U d p hm (fun z => (u z : ℝ)))) label k s u
          ∑ t : terms × (∀ j, ((coverWitness r).expansion j).Term), ∑ label : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period))), ∑ k,
            (c t * (allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative refined d period cI) label k) * ∏ s,
              test s (fun z => (physicalCubeVertexValue u s z : ℝ)) *
                Ψ t label k s (physicalCubeVertexValue u s)

noncomputable def allocatedAmbientNormalizedSpatialApproximation
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (u : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
    let c := fun t : terms × (∀ j, ((coverWitness r).expansion j).Term) =>
      (coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
        coverSiteCoefficient (coverWitness r).expansion t.2
    ∑ t : terms × (∀ i, ((coverWitness r).expansion i).Term),
      ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, Kcov j → ZMod period)),
        ∑ k : K,
          ∑ gridLabel : Finset (Fin dim) → ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i)),
            (c t * allocatedProductMaskedIdealCoefficient B U b S rowSets x
              (coverWitness r).representative refined d period cI label k) *
              ∏ s, test s (fun z => (physicalCubeVertexValue u s z : ℝ)) *
                allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
                  hb o bW d x N mesh base p hm r a.val period t.1 t.2 (label s) (fI k s) s
                  (gridLabel s) (physicalCubeVertexValue u s)

omit [∀ (i : {i // allocatedGridAxis (I := I) U b S.value i})
  (ki : ((coverWitness r).expansion i).Term), NeZero (((coverWitness r).expansion i).period ki)] in
theorem allocatedAmbientMaskedSpatialApproximation_reconstruction
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedAmbientMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
      coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period cI fI test (point v) =
    allocatedRecenteredMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
      coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period cI fI test v := rfl

theorem allocatedAmbientNormalizedSpatialApproximation_reconstruction
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
      coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI test (point v) =
    allocatedRecenteredNormalizedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
      coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI test v := rfl

local notation "ig" => allocatedGridIntegerAxis B U b S

include hR in
theorem allocatedAmbientMaskedSpatialApproximation_normalized
    (hsite : ∀ kg s (u₀ : ∀ j, euclideanSubspace (U j)) (w₀ : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)),
      (∀ j, (QuotientAddGroup.mk (u₀ j) : euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) =
        normalizedLatticeQuotient (euclideanSubspace (U j)) (b j) (hb j) (orthonormalMixedChart (o j) (w₀ j))) →
      (∀ j i, |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) (w₀ j)) i| ≤ 1 / 4) →
      g r kg s (fun v => ((((u₀ v.1).val v.2) / commonSitePeriod (coverWitness r).expansion kg : ℝ) : UnitAddCircle)) =
        allocatedFullGridSiteFactor (G := G) B U b (R := R) (coverWitness r).expansion ig kg s
          (fun i => ((w₀ (ig i).1).2 (ig i).2 : ZMod (((coverWitness r).expansion i).period (kg i))))
          (allocatedFullMixedSiteValue (R := R) U b w₀) / 2)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ C j * ‖w‖)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j)
    (hN : ∀ z, 0 < N z)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (u : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedAmbientMaskedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
      coverWitness hb o bW d g x hM selection hx N hW mesh base cells p hm r a period cI fI test u =
    allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S X modulus q wholeReference
      coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI test u := by
  unfold allocatedAmbientMaskedSpatialApproximation allocatedAmbientNormalizedSpatialApproximation
  dsimp only
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (s : Finset (Fin dim))
    (gl : ∀ i, ZMod (((coverWitness r).expansion i).period (t.2 i))) =>
      test s (fun z => (physicalCubeVertexValue u s z : ℝ)) *
        allocatedRecenteredNormalizedSiteFactor (τ := τ) B U b S X modulus q wholeReference coverWitness
          hb o bW d x N mesh base p hm r a.val period t.1 t.2 (label s) (fI k s) s gl
          (physicalCubeVertexValue u s))]
  apply congrArg (fun z : ℂ =>
    ((coeff (principalResidueLabel modulus (wholeReference r.val)) t.1 / ((volume : ℝ) : ℂ)) *
      coverSiteCoefficient (coverWitness r).expansion t.2 *
      allocatedProductMaskedIdealCoefficient B U b S rowSets x (coverWitness r).representative
        refined d period cI label k) * z)
  apply Finset.prod_congr rfl
  intro s _
  rw [← Finset.mul_sum]
  apply congrArg (fun z : ℂ =>
    test s (fun z => (physicalCubeVertexValue u s z : ℝ)) * z)
  exact allocatedRecenteredNormalizedSiteFactor_sum (τ := τ) B U b S X modulus q wholeReference coverWitness
    hb o bW d x N mesh base p hm r a.val period t.1 t.2 (label s) (fI k s) s
    (g r t.2 s) (hsite t.2 s) hR C hC hchart hsmall hN (physicalCubeVertexValue u s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  (∀ a, ((coverWitness r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ))
variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ≥0) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "point" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r.val a.val
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

variable (period : ℕ) [NeZero period]
variable {K : Type*} [Fintype K] (cI : K → ℂ)
variable (fI : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)

local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

variable [∀ (i : {i // allocatedGridAxis (I := I) U b S.value i})
  (ki : ((coverWitness r).expansion i).Term), NeZero (((coverWitness r).expansion i).period ki)]

local notation "ambient" => allocatedAmbientNormalizedSpatialApproximation (τ := τ) B U b S X modulus q
  wholeReference coverWitness hb o bW d x hM selection hx N hW mesh base cells p hm r a period cI fI

theorem allocatedAmbientNormalizedSpatialApproximation_test_congr
    (test other : Finset (Fin dim) → (X → ℝ) → ℂ) (u : X → (Unit ⊕ Fin dim) → ℤ)
    (heq : ∀ s, test s (fun z => (physicalCubeVertexValue u s z : ℝ)) =
      other s (fun z => (physicalCubeVertexValue u s z : ℝ))) :
    ambient test u = ambient other u := by
  unfold allocatedAmbientNormalizedSpatialApproximation
  dsimp only
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro gridLabel _
  congr 1
  apply Finset.prod_congr rfl
  intro s _
  rw [heq s]

theorem allocatedAmbientNormalizedSpatialApproximation_zero_of_test_zero
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (u : X → (Unit ⊕ Fin dim) → ℤ)
    (s₀ : Finset (Fin dim)) (hzero : test s₀ (fun z => (physicalCubeVertexValue u s₀ z : ℝ)) = 0) :
    ambient test u = 0 := by
  unfold allocatedAmbientNormalizedSpatialApproximation
  dsimp only
  apply Finset.sum_eq_zero
  intro t _
  apply Finset.sum_eq_zero
  intro label _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro gridLabel _
  apply mul_eq_zero.mpr
  right
  apply Finset.prod_eq_zero (Finset.mem_univ s₀)
  rw [hzero, zero_mul]

variable [DecidableEq X]

theorem allocatedAmbientNormalizedSpatialApproximation_testExtension_eq
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (u : X → (Unit ⊕ Fin dim) → ℤ)
    (hu : u ∈ physicalIntegerBoxCubes N dim) :
    ambient (fun s => integerBoxTestExtension N (test s)) u = ambient test u := by
  apply allocatedAmbientNormalizedSpatialApproximation_test_congr
  intro s
  exact integerBoxTestExtension_of_mem N (test s) (physicalCubeVertexValue u s)
    ((mem_physicalIntegerBoxCubes N dim u).mp hu s)

theorem allocatedAmbientNormalizedSpatialApproximation_testExtension_nonzero_mem_box
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) (u : X → (Unit ⊕ Fin dim) → ℤ)
    (hu : ambient (fun s => integerBoxTestExtension N (test s)) u ≠ 0) :
    u ∈ physicalIntegerBoxCubes N dim := by
  apply (mem_physicalIntegerBoxCubes N dim u).mpr
  intro s
  by_contra hs
  apply hu
  exact allocatedAmbientNormalizedSpatialApproximation_zero_of_test_zero
    B U b S X modulus q wholeReference coverWitness hb o bW d x hM selection hx N hW mesh
    base cells p hm r a period cI fI (fun s => integerBoxTestExtension N (test s)) u s
    (integerBoxTestExtension_of_not_mem N (test s) (physicalCubeVertexValue u s) hs)

end Erdos3.VectorPolynomial

end

end OAI
