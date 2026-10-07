import OAI.Combinatorics.Progressions.Estimates.AllocatedWeightedProfileError
import OAI.Combinatorics.Progressions.Geometry.AllocatedReferenceSpatialRemeshing

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_profile_sum_sub {T : Type*} [Fintype T]
    (a : T → ℂ) (f g : T → ℝ) :
    ‖(∑ t, a t * (f t : ℂ)) - ∑ t, a t * (g t : ℂ)‖ ≤
      ∑ t, ‖a t‖ * |f t - g t| := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t _
  rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem norm_nested_profile_reference_sub {Ω R T : Type*}
    [Fintype Ω] [Fintype R] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights R)
    (a : Ω → R → T → ℂ) (f g : Ω → R → T → ℝ)
    {E Z : ℝ} (hZ : 0 < Z)
    (he : ∀ u r, (∑ t, ‖a u r t‖ * |f u r t - g u r t|) ≤ E) :
    ‖p.complexMean (fun u => q.complexMean (fun r => ∑ t, a u r t * (f u r t : ℂ))) / (Z : ℂ) -
      p.complexMean (fun u => q.complexMean (fun r => ∑ t, a u r t * (g u r t : ℂ))) / (Z : ℂ)‖ ≤ E / Z := by
  have hi (u) : ‖q.complexMean (fun r => ∑ t, a u r t * (f u r t : ℂ)) -
      q.complexMean (fun r => ∑ t, a u r t * (g u r t : ℂ))‖ ≤ E := by
    exact (q.norm_complexMean_sub_le _ _ (fun _ => E)
      (fun r _ => (norm_profile_sum_sub (a u r) (f u r) (g u r)).trans (he u r))).trans_eq (q.mean_const E)
  have ho := (p.norm_complexMean_sub_le _ _ (fun _ => E) (fun u _ => hi u)).trans_eq (p.mean_const E)
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  exact div_le_div_of_nonneg_right ho hZ.le

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

omit [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
  [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
  [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
  [NeZero modulus] [NeZero (residueRefinedPeriod modulus q)]
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedRefinedReferenceProfile_as_covered
    (u : PrincipalAxisTuples (α := Fin dim) grid sides)
    (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) :
    allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d u r =
      allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) rows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (allocatedLongProfileDensity B U b S x rows modulus (residue u r)
          (allocatedContinuousLongJetProxy B U b S x u rows s hA)) := by
  simp only [allocatedRefinedReferenceProfile, allocatedCoveredProfileDensity, allocatedLongProfileDensity_proxy]
  rfl

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

local notation "frozenTuple" => PrincipalAxisTuples (α := Fin dim) grid sides
local notation "label" => (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

noncomputable def allocatedRefinedProfileCoefficient (u : frozenTuple) (r : label)
    (t : cells × window) : ℂ :=
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  (selectedResidueCellWeight q cells V t.1 : ℂ) *
    (allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW mesh u r t.2.val / (A : ℂ)) *
    test (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val)

noncomputable def allocatedRefinedCoveredReference
    (profile : frozenTuple → label → EuclideanJetLayers U O → ℝ) : ℂ :=
  (frozen).complexMean (fun u =>
    ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).complexMean (fun r =>
      ∑ t : cells × window,
        allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
          reference N hW mesh base cells test u r t *
        (profile u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val)) : ℂ))) /
    (Z : ℂ)

noncomputable def allocatedRefinedCoveredError
    (f g : frozenTuple → label → EuclideanJetLayers U O → ℝ) (u : frozenTuple) (r : label) : ℝ :=
  ∑ t : cells × window,
    ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
      reference N hW mesh base cells test u r t‖ *
    |f u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val)) -
      g u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))|

theorem allocatedRefinedTupleReference_as_coveredReference :
    allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
      N hW mesh base cells point test Z =
    allocatedRefinedCoveredReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
      (allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d) := by
  rfl

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedCoveredReference_error
    (f g : frozenTuple → label → EuclideanJetLayers U O → ℝ) {E : ℝ}
    (hZ : 0 < Z)
    (he : ∀ u r, allocatedRefinedCoveredError (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test f g u r ≤ E) :
    ‖allocatedRefinedCoveredReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z f -
      allocatedRefinedCoveredReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z g‖ ≤ E / Z := by
  exact norm_nested_profile_reference_sub _ _ _ _ _ hZ he

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

noncomputable def allocatedRefinedIdealProfile (δ : ℝ≥0) :=
  fun u r => allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) rows hb o bW d
    (fun j _ => standardLatticeClosedQuarterBox (J j))
    (allocatedLongProfileDensity B U b S x rows modulus (residue u r)
      (physicalActiveProfileIdeal (G := G) (B := B) (G × Option (Fin dim)) (layerSamplerDegree I n)
        grid (fun a => rows a.val.1) (fun a => R a.1) (fun a => hR a.1) δ))

noncomputable def allocatedRefinedIdealReference (δ : ℝ≥0) : ℂ :=
  allocatedRefinedCoveredReference (τ := τ) (ξ := ξ)
    B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
    (allocatedRefinedIdealProfile B U b hR hσ S x rows X modulus q reference residue hb o bW d δ)

theorem allocatedRefinedTupleReference_ideal_error (δ : ℝ≥0) {E : ℝ} (hZ : 0 < Z)
    (he : ∀ u r, allocatedRefinedCoveredError (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test
      (allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d)
      (allocatedRefinedIdealProfile B U b hR hσ S x rows X modulus q reference residue hb o bW d δ) u r ≤ E) :
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW mesh base cells point test Z -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point test Z δ‖ ≤ E / Z := by
  rw [allocatedRefinedTupleReference_as_coveredReference]
  exact allocatedRefinedCoveredReference_error B U b S x X hM selection hx modulus q reference
    N hW mesh base cells point test Z _ _ hZ he

theorem allocatedRefinedTupleReference_ideal_exp_error (δ : ℝ≥0)
    {P E Fsp Merr δf ε : ℝ}
    (hFsp0 : 0 ≤ Fsp) (hFsp : Fsp ≤ Real.exp (coefficientErrorSpatialLog P))
    (hMerr : Merr ≤ profileReferenceAccuracy P E)
    (hδf : δf ≤ profileReferenceAccuracy P E) (hε : ε ≤ profileReferenceAccuracy P E)
    (hZ : 1 / 2 ≤ Z)
    (he : ∀ u r, allocatedRefinedCoveredError (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test
      (allocatedRefinedReferenceProfile B U b hR hσ S x rows X modulus s hA q reference residue hb o bW d)
      (allocatedRefinedIdealProfile B U b hR hσ S x rows X modulus q reference residue hb o bW d δ) u r ≤
        Fsp * (Merr + 2 * δf + ε)) :
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW mesh base cells point test Z -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point test Z δ‖ ≤ Real.exp (-E) := by
  have hZ0 : 0 < Z := by linarith
  exact (allocatedRefinedTupleReference_ideal_error B U b hR hσ S x rows X hM selection hx modulus
    s hA q reference residue hb o bW d N hW mesh base cells point test Z δ hZ0 he).trans
    (profileReferenceAccuracy_normalized_error hFsp0 hFsp hMerr hδf hε hZ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_reference_profile_window_bound :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
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
    {P Rrank ε : ℝ} (_hP : 0 ≤ P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (_hτP : 1 / τ ≤ Real.exp P) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp P)
    (_hsize : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((P + K) ^ K) ≤ Rrank)
    (spatialMesh : ℝ) (_hspatialMesh : 0 < spatialMesh)
    (Cm : ℝ≥0) (_hCm : 1 ≤ (Cm : ℝ))
    (_hmasks : ∀ u r j z, 0 ≤ allocatedIntegerKernelMask B U b S x jetRows j modulus (residue u r j) z ∧
      allocatedIntegerKernelMask B U b S x jetRows j modulus (residue u r j) z ≤ Cm)
    (profile₁ profile₂ : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S) →
      ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, jets a.val.1) → ℝ) → ℝ)
    (Cf Cg Kf Kg : ℝ≥0)
    (_hf : ∀ u, LipschitzWith Kf (profile₁ u)) (_hg : ∀ u, LipschitzWith Kg (profile₂ u))
    (_hfb : ∀ u z, |profile₁ u z| ≤ Cf) (_hgb : ∀ u z, |profile₂ u z| ≤ Cg)
    {δf L : ℝ} (_hδf : 0 < δf) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ L) (_hδL : δf⁻¹ ≤ Real.exp L),
    let A := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus) * Cm ^ Fintype.card (LayerSamplerAxis I n)
    (allocatedProfileErrorLip B U b S (O := jets) A Cf Cg Kf Kg C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := jets) A Cf Cg V ≤ Real.exp P →
    (∀ u, Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun z => |profile₁ u z - profile₂ u z|))
      (allocatedLongJetReference B U b S jets)) →
    ∀ Merr : ℝ,
    (∀ u, (A : ℝ) * (∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun v => |profile₁ u v - profile₂ u v|) z
      ∂allocatedLongJetReference B U b S jets) ≤ Merr) →
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    let Csp := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (Mk : ℝ))) ^ Fintype.card X
    ∀ test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ, (∀ w, ‖test w‖ ≤ 1) → ∀ u r,
    allocatedRefinedCoveredError (τ := τ) (ξ := ξ)
      B U b S x X hMk selection hx modulus q reference N _hW spatialMesh base cells
      (physicalCubeEuclideanSample U d p hm) test
      (fun u r => allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (allocatedLongProfileDensity B U b S x jetRows modulus (residue u r) (profile₁ u)))
      (fun u r => allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (allocatedLongProfileDensity B U b S x jetRows modulus (residue u r) (profile₂ u))) u r ≤
      Csp * (Vsp * (Merr + 2 * δf + ε)) := by
  obtain ⟨K, hK, htail⟩ := exists_allocated_weighted_profile_error m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x Mk hMk selection hx _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod hperiodSp X _ _ q hq reference residue N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    hbudget base cells hmass p hp hm P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    spatialMesh hspatialMesh Cm hCm hmasks profile₁ profile₂ Cf Cg Kf Kg hf hg hfb hgb
    δf L hδf hL hamb hδL A hLip hfreqP hcoeffP hi Merr hMerr Vsp Csp test htest u r
  let _ := coefficientTorus_compact_of_lattice (K := Fin dim) U
  let _ : MeasurableSpace (CoefficientTorus (K := Fin dim) U) := borel _
  let _ : BorelSpace (CoefficientTorus (K := Fin dim) U) := ⟨rfl⟩
  let H := trimmedSpatialRootScale τ N q
  let T := trimmedSpatialSlopeScale W τ N q
  let Vs := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let y := principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u (reference u r)
  have hgeo (t : X) := allocatedNarrow_reference_jet_geometry B U b S (fun _ => 0) x y N q hN hq
    hW hτ hξ1 hρ hsizeSp hρ8 hρshift t
  have hH (t) : 0 < H t := (hgeo t).1
  have hT (t) : 0 < T t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2
  have hCsp : 0 ≤ Csp := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection (by positivity))) _
  have hsp : ∀ w ∈ spatialWindow H 4,
      ‖allocatedRefinedSpatialKernel (τ := τ) B U b S x X hMk selection hx modulus q reference N hW spatialMesh u r w‖ ≤ Csp :=
    allocatedReferenceSpatialProxy_bound B U b S x y hMk selection hx modulus hperiodSp H hH hW hbudget hspatialMesh
  have h := htail hP hX hdim U (probabilityAddHaar _) ν p hp hm d q hq
    (Real.exp_pos P).le le_rfl hτ hε hτP hεP hstride (fun t => (N t : ℝ)) hsize hrank hRank
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) (allocatedPhysicalCubeDirections B U b S x y)
    base cells Vs (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass H T hH hT
    (Nat.cast_pos.mpr S.positive) (trimmedSpatial_scale_ratio hW N q)
    (fun t => (hgeo t).2.1) (fun t => (hgeo t).2.2.1) (fun t => (hgeo t).2.2.2)
    (allocatedRefinedSpatialKernel (τ := τ) B U b S x X hMk selection hx modulus q reference N hW spatialMesh u r)
    hCsp hsp test htest
    B b S o hR hσ x u (reference u r) jetRows hb bW modulus hperiod modulus (residue u r)
    Cm hCm (hmasks u r) (profile₁ u) (profile₂ u) (hf u) (hg u) (hfb u) (hgb u)
    C V hC hV hδf hL hamb hδL hLip hfreqP hcoeffP (hi u) Merr (hMerr u)
  exact h

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

local notation "frozenTuple" => PrincipalAxisTuples (α := Fin dim) grid sides
local notation "label" => (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

noncomputable def allocatedRefinedComplexReference
    (profile : frozenTuple → label → EuclideanJetLayers U O → ℂ) : ℂ :=
  (frozen).complexMean (fun u =>
    ((long).fiberLaw (principalResidueLabel (residueRefinedPeriod modulus q))).complexMean (fun r =>
      ∑ t : cells × window,
        allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
          reference N hW mesh base cells test u r t *
        profile u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val)))) /
    (Z : ℂ)

noncomputable def allocatedRefinedComplexError
    (f g : frozenTuple → label → EuclideanJetLayers U O → ℂ) (u : frozenTuple) (r : label) : ℝ :=
  ∑ t : cells × window,
    ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
      reference N hW mesh base cells test u r t‖ *
    ‖f u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val)) -
      g u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))‖

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedComplexReference_real
    (f : frozenTuple → label → EuclideanJetLayers U O → ℝ) :
    allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
      (fun u r y => (f u r y : ℂ)) =
    allocatedRefinedCoveredReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z f := rfl

omit [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedIdealReference_as_complex (δ : ℝ≥0) :
    allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
      N hW mesh base cells point test Z δ =
    allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
      (fun u r y => (allocatedRefinedIdealProfile B U b hR hσ S x rows X modulus q reference residue hb o bW d δ u r y : ℂ)) := rfl

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedComplexReference_error
    (f g : frozenTuple → label → EuclideanJetLayers U O → ℂ) {E : ℝ}
    (hZ : 0 < Z)
    (he : ∀ u r, allocatedRefinedComplexError (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test f g u r ≤ E) :
    ‖allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z f -
      allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z g‖ ≤ E / Z := by
  exact norm_nested_complex_profile_reference_sub _ _ _ _ _ hZ he

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedComplexReference_sum {T : Type*} [Fintype T]
    (c : T → ℂ) (F : T → frozenTuple → label → EuclideanJetLayers U O → ℂ) :
    allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
      (fun u r y => ∑ i, c i * F i u r y) =
    ∑ i, c i * allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z (F i) := by
  have hsum (u : frozenTuple) (r : label) :
      (∑ t : cells × window,
        allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
          reference N hW mesh base cells test u r t *
          ∑ i, c i * F i u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))) =
      ∑ i, c i * ∑ t : cells × window,
        allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
          reference N hW mesh base cells test u r t *
          F i u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp only [allocatedRefinedComplexReference, hsum, finiteComplexMean_sum,
    finiteComplexMean_const_mul, Finset.sum_div, mul_div_assoc]

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedComplexReference_pointwise_error
    (f g : frozenTuple → label → EuclideanJetLayers U O → ℂ)
    (envelope : frozenTuple → label → EuclideanJetLayers U O → ℝ)
    {ε mass : ℝ} (hε : 0 ≤ ε) (hZ : 0 < Z)
    (hpoint : ∀ u r y, ‖f u r y - g u r y‖ ≤ ε * envelope u r y)
    (hmass : ∀ u r, (∑ t : cells × window,
      ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
        reference N hW mesh base cells test u r t‖ *
      envelope u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))) ≤ mass) :
    ‖allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z f -
      allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z g‖ ≤ (ε * mass) / Z := by
  apply allocatedRefinedComplexReference_error B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z f g hZ
  intro u r
  unfold allocatedRefinedComplexError
  calc
    _ ≤ ∑ t : cells × window,
      ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
        reference N hW mesh base cells test u r t‖ *
      (ε * envelope u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))) := by
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (hpoint u r _) (norm_nonneg _)
    _ = ε * ∑ t : cells × window,
      ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
        reference N hW mesh base cells test u r t‖ *
      envelope u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hmass u r) hε

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

local notation "frozenTuple" => PrincipalAxisTuples (α := Fin dim) grid sides
local notation "label" => (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedComplexReference_const_mul
    (c : ℂ) (F : frozenTuple → label → EuclideanJetLayers U O → ℂ) :
    allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
      (fun u r y => c * F u r y) =
    c * allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z F := by
  simpa using allocatedRefinedComplexReference_sum (τ := τ) (ξ := ξ)
    B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
    (T := Unit) (fun _ => c) (fun _ => F)

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

local notation "frozenTuple" => PrincipalAxisTuples (α := Fin dim) grid sides
local notation "label" => (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable {T Y : Type*} [Fintype T]

omit [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedIdealReference_site_error
    (c : T → ℂ)
    (site : frozenTuple → label → EuclideanJetLayers U O → Finset (Fin dim) → Y)
    (factor : T → frozenTuple → label → Finset (Fin dim) → Y → ℂ)
    (envelope : frozenTuple → label → EuclideanJetLayers U O → ℝ)
    (δ : ℝ≥0) {ε mass : ℝ} (hε : 0 ≤ ε) (hZ : 0 < Z)
    (hpoint : ∀ u r y,
      ‖(allocatedRefinedIdealProfile B U b hR hσ S x rows X modulus q reference residue hb o bW d δ u r y : ℂ) -
        ∑ i : T, c i * ∏ v : Finset (Fin dim), factor i u r v (site u r y v)‖ ≤ ε * envelope u r y)
    (hmass : ∀ u r, (∑ t : cells × window,
      ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
        reference N hW mesh base cells test u r t‖ *
      envelope u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))) ≤ mass) :
    ‖allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point test Z δ -
      ∑ i : T, c i * allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
        (fun u r y => ∏ v : Finset (Fin dim), factor i u r v (site u r y v))‖ ≤ (ε * mass) / Z := by
  rw [allocatedRefinedIdealReference_as_complex, ← allocatedRefinedComplexReference_sum]
  exact allocatedRefinedComplexReference_pointwise_error B U b S x X hM selection hx modulus q
    reference N hW mesh base cells point test Z _ _ envelope hε hZ hpoint hmass

theorem allocatedRefinedTupleReference_site_error
    (c : T → ℂ)
    (site : frozenTuple → label → EuclideanJetLayers U O → Finset (Fin dim) → Y)
    (factor : T → frozenTuple → label → Finset (Fin dim) → Y → ℂ)
    (envelope : frozenTuple → label → EuclideanJetLayers U O → ℝ)
    (δ : ℝ≥0) {ε mass E : ℝ} (hε : 0 ≤ ε) (hZ : 0 < Z)
    (hbefore : ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW mesh base cells point test Z -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
        N hW mesh base cells point test Z δ‖ ≤ E)
    (hpoint : ∀ u r y,
      ‖(allocatedRefinedIdealProfile B U b hR hσ S x rows X modulus q reference residue hb o bW d δ u r y : ℂ) -
        ∑ i : T, c i * ∏ v : Finset (Fin dim), factor i u r v (site u r y v)‖ ≤ ε * envelope u r y)
    (hmass : ∀ u r, (∑ t : cells × window,
      ‖allocatedRefinedProfileCoefficient (τ := τ) (ξ := ξ) B U b S x X hM selection hx modulus q
        reference N hW mesh base cells test u r t‖ *
      envelope u r (point (allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r t.1 t.2.val))) ≤ mass) :
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x rows X hM selection hx modulus s hA q reference residue hb o bW d
        N hW mesh base cells point test Z -
      ∑ i : T, c i * allocatedRefinedComplexReference (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test Z
        (fun u r y => ∏ v : Finset (Fin dim), factor i u r v (site u r y v))‖ ≤ E + (ε * mass) / Z := by
  have hafter := allocatedRefinedIdealReference_site_error B U b hR hσ S x rows X hM selection hx
    modulus q reference residue hb o bW d N hW mesh base cells point test Z c site factor envelope δ hε hZ hpoint hmass
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hbefore hafter)

end Erdos3.VectorPolynomial

end

end OAI
