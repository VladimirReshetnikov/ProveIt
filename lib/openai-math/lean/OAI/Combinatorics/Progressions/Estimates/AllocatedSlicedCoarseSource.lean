import OAI.Combinatorics.Progressions.Geometry.AllocatedSpatialTermSupport
import OAI.Combinatorics.Progressions.Geometry.CoarseSpatialPartitionBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_reconstruction_shift {V Y : Type*} [AddCommGroup V] [DecidableEq V]
    (window : Finset V) (weight : V → ℂ) (f g : V → Y) (test : Y → ℂ)
    (s : V) (hrec : ∀ v, f v = g (v + s)) :
    (∑ v ∈ window, weight v * test (f v)) =
      ∑ v ∈ window.image (fun w => w + s), weight (v - s) * test (g v) := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v _
    rw [add_sub_cancel_right, hrec]
  · intro a _ b _ he
    exact add_right_cancel he

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

noncomputable def allocatedTranslatedProfileTerm
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) : ℂ :=
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  ∑ a : cells,
    let shift := allocatedResidueReferenceShift B U b S X modulus q reference wholeReference x y a.val
    (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ (window).image (fun w => w + shift),
        (allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus y) (v - shift) / (A : ℂ)) *
        test (reconstruct a.val v) * profile y (point (reconstruct a.val v))

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedResidueWeightedProfileTerm_translate
    (hq : ∀ t, 0 < q t)
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (hwhole : ∀ r, principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) :
    allocatedResidueWeightedProfileTerm (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile y =
    allocatedTranslatedProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q reference wholeReference x hM selection hx N hW mesh base cells point test profile y := by
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  unfold allocatedResidueWeightedProfileTerm allocatedTranslatedProfileTerm
  dsimp only
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  let shift := allocatedResidueReferenceShift B U b S X modulus q reference wholeReference x y a.val
  let oldR := allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells
    (principalAxisRestrict grid y) (principalResidueLabel refined (principalAxisRestrict (fun a => ¬grid a) y)) a
  let newR := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y) a.val
  let term := fun v : X → (Unit ⊕ Fin dim) → ℤ =>
    (selectedResidueCellWeight q cells V a : ℂ) *
      (allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
        (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus y) v / (A : ℂ)) *
      test (oldR v) * profile y (point (oldR v))
  change (∑ v : window, term v.val) = _
  rw [← Finset.sum_subtype (window) (fun _ => Iff.rfl) term]
  have hrec : ∀ v, oldR v = newR (v + shift) :=
    (allocatedResidueReferenceShift_spec B U b S X modulus q reference wholeReference x hq href hwhole
      base y a.val).2.1
  have heq := finite_reconstruction_shift window
    (fun v => allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
      (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus y) v / (A : ℂ))
    oldR newR (fun v => test v * profile y (point v)) shift hrec
  have h := congrArg (fun z : ℂ => (selectedResidueCellWeight q cells V a : ℂ) * z) heq
  simpa only [term, oldR, newR, shift, A, V, Finset.mul_sum, mul_assoc] using h

theorem allocatedResidueWeightedReference_translate
    (hq : ∀ t, 0 < q t)
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (hwhole : ∀ r, principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (Z : ℝ) :
    (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides
      (allocatedPrincipalSides_pos B U b S)).complexMean
      (allocatedResidueWeightedProfileTerm (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile) / (Z : ℂ) =
    (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides
      (allocatedPrincipalSides_pos B U b S)).complexMean
      (allocatedTranslatedProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q reference wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ) := by
  apply congrArg (fun z : ℂ => z / (Z : ℂ))
  apply congrArg (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides
    (allocatedPrincipalSides_pos B U b S)).complexMean
  funext y
  exact allocatedResidueWeightedProfileTerm_translate B U b S X modulus q reference wholeReference x
    hM selection hx N hW mesh base cells point test hq href hwhole profile y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedResidueWeightedProfileTerm_translate_at
    (hq : ∀ t, 0 < q t)
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple)
    (hwhole : principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) =
      principalResidueLabel refined y) :
    allocatedResidueWeightedProfileTerm (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile y =
    allocatedTranslatedProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q reference wholeReference x hM selection hx N hW mesh base cells point test profile y := by
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  unfold allocatedResidueWeightedProfileTerm allocatedTranslatedProfileTerm
  dsimp only
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  let shift := allocatedResidueReferenceShift B U b S X modulus q reference wholeReference x y a.val
  let oldR := allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells
    (principalAxisRestrict grid y) (principalResidueLabel refined (principalAxisRestrict (fun a => ¬grid a) y)) a
  let newR := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y) a.val
  let term := fun v : X → (Unit ⊕ Fin dim) → ℤ =>
    (selectedResidueCellWeight q cells V a : ℂ) *
      (allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
        (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus y) v / (A : ℂ)) *
      test (oldR v) * profile y (point (oldR v))
  change (∑ v : window, term v.val) = _
  rw [← Finset.sum_subtype (window) (fun _ => Iff.rfl) term]
  have hrec : ∀ v, oldR v = newR (v + shift) :=
    (allocatedResidueReferenceShift_spec_at B U b S X modulus q reference wholeReference x hq href
      base y hwhole a.val).2.1
  have heq := finite_reconstruction_shift window
    (fun v => allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
      (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus y) v / (A : ℂ))
    oldR newR (fun v => test v * profile y (point v)) shift hrec
  have h := congrArg (fun z : ℂ => (selectedResidueCellWeight q cells V a : ℂ) * z) heq
  simpa only [term, oldR, newR, shift, A, V, Finset.mul_sum, mul_assoc] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

noncomputable def allocatedRecenteredProfileTerm
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) : ℂ :=
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
    ∑ v ∈ window,
      (allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
        (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus y) v / (A : ℂ)) *
      test (reconstruct a.val v) * profile y (point (reconstruct a.val v))

noncomputable def allocatedRecenteredProfileMass
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) : ℝ :=
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  ∑ a : cells, selectedResidueCellWeight q cells V a *
    ((∑ v ∈ window, ‖profile y (point (reconstruct a.val v))‖) / A)

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
variable (href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
variable (hwhole : ∀ r, principalResidueLabel (residueRefinedPeriod modulus q) (wholeReference r) = r)
variable (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage
    (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hmesh : 0 < mesh) {ε : ℝ} (hε : 0 ≤ ε) (hmargin : (3 + 2 * mesh) + 2 * ε ≤ 4)
variable (hsize : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ ε * trimmedSpatialRootScale τ N q t)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "shiftError" => Fintype.card X *
  ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (8 * mesh + ε)) *
  (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X

include hq hN hτ href hwhole hQ hratio hbudget hperiod hmesh hε hmargin hsize htest in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedTranslatedProfileTerm_recenter_error
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) :
    ‖allocatedTranslatedProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q reference wholeReference x hM selection hx N hW mesh base cells point test profile y -
      allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y‖ ≤
      shiftError * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile y := by
  let H := trimmedSpatialRootScale τ N q
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t)
    (trimmedSpatialSlopeScale W τ N q t) S.value i
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let K := allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh (principalResidueLabel modulus y)
  let recons := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base (principalResidueLabel refined y)
  let shift := fun a : cells => allocatedResidueReferenceShift B U b S X modulus q reference wholeReference x y a.val
  have hH (t) : 0 < H t := (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
  have hA : 0 < A := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hH t)
      (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2 (Nat.cast_pos.mpr S.positive) i))
  have hE : 0 ≤ shiftError := by
    have hκ : 0 ≤ 1 / (M : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg M)
    have hLip := anisotropicSpatialDensityLip_nonneg selection hκ
    have hCap := anisotropicSpatialDensityCap_nonneg selection hκ
    positivity
  have hcell (a : cells) :
      ‖(∑ v ∈ (window).image (fun w => w + shift a), (K (v - shift a) / (A : ℂ)) *
          test (recons a.val v) * profile y (point (recons a.val v))) -
        ∑ v ∈ window, (K v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v))‖ ≤
      (shiftError * (∑ v ∈ window, ‖profile y (point (recons a.val v))‖)) / A := by
    have hnormalized := allocatedResidueReferenceShift_normalized B U b S X modulus q reference wholeReference x
      hq href hwhole H hH hε hsize y a.val
    have hlattice := (allocatedResidueReferenceShift_spec B U b S X modulus q reference wholeReference x
      hq href hwhole base y a.val).1
    have hs : shift a ∈ spatialWindow H (2 * ε) := by
      apply spatialWindow_of_coordinate_bound H (fun t => (hH t).le) hε (shift a)
      intro t i
      have h := (norm_le_pi_norm _ i).trans (hnormalized t)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (hH t)] at h
      simpa only [mul_comm] using (div_le_iff₀ (hH t)).mp h
    have hglobal := allocatedResidueSpatialKernel_shift_global B U b S x X hM selection hx modulus H hW mesh
      Q hQ hratio hbudget hperiod hH hmesh hε hmargin (principalResidueLabel modulus y)
      (shift a) hlattice hnormalized
    have hsupp := allocatedResidueSpatialKernel_zero_outside B U b S x X hM selection hx modulus H hW mesh
      hbudget hH hmesh (principalResidueLabel modulus y)
    have hraw := spatialWeight_shifted_window_error H (fun t => (hH t).le) K
      (fun v => test (recons a.val v) * profile y (point (recons a.val v)))
      (by positivity : 0 ≤ 2 * ε) hmargin hsupp (shift a) hs hglobal
    have hmass : (∑ v ∈ window, ‖test (recons a.val v) * profile y (point (recons a.val v))‖) ≤
        ∑ v ∈ window, ‖profile y (point (recons a.val v))‖ := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (htest _) (norm_nonneg _)).trans_eq (one_mul _)
    have hd := div_le_div_of_nonneg_right (hraw.trans (mul_le_mul_of_nonneg_left hmass hE)) hA.le
    simpa only [div_mul_eq_mul_div, ← Finset.sum_div, ← sub_div, norm_div,
      Complex.norm_real, Real.norm_of_nonneg hA.le, mul_assoc] using hd
  change ‖(∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ (window).image (fun w => w + shift a), (K (v - shift a) / (A : ℂ)) *
        test (recons a.val v) * profile y (point (recons a.val v))) -
    (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window, (K v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v)))‖ ≤
    shiftError * ∑ a : cells, selectedResidueCellWeight q cells V a *
      ((∑ v ∈ window, ‖profile y (point (recons a.val v))‖) / A)
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a : cells, selectedResidueCellWeight q cells V a *
        ((shiftError * (∑ v ∈ window, ‖profile y (point (recons a.val v))‖)) / A) := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (selectedResidueCellWeight_nonneg q cells V a)]
      exact mul_le_mul_of_nonneg_left (hcell a) (selectedResidueCellWeight_nonneg q cells V a)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

include hq hN hτ href hwhole hQ hratio hbudget hperiod hmesh hε hmargin hsize htest in
theorem allocatedTranslatedReference_recenter_error
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (Z : ℝ) (hZ : 0 < Z) :
    ‖(whole).complexMean
        (allocatedTranslatedProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q reference wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ) -
      (whole).complexMean
        (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)‖ ≤
      shiftError * (whole).mean
        (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x N base cells point profile) / Z := by
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  apply div_le_div_of_nonneg_right _ hZ.le
  have h := (whole).norm_complexMean_sub_le
    (allocatedTranslatedProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q reference wholeReference x hM selection hx N hW mesh base cells point test profile)
    (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)
    (fun y => shiftError * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile y)
    (fun y _ => by apply allocatedTranslatedProfileTerm_recenter_error <;> assumption)
  simpa only [FiniteProbabilityWeights.mean_const_mul] using h

include hq hN hτ href hwhole hQ hratio hbudget hperiod hmesh hε hmargin hsize htest in
theorem allocatedResidueWeightedReference_recenter_error
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (Z : ℝ) (hZ : 0 < Z) :
    ‖(whole).complexMean
        (allocatedResidueWeightedProfileTerm (τ := τ) (ξ := ξ)
          B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile) / (Z : ℂ) -
      (whole).complexMean
        (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)‖ ≤
      shiftError * (whole).mean
        (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x N base cells point profile) / Z := by
  rw [allocatedResidueWeightedReference_translate B U b S X modulus q reference wholeReference x
    hM selection hx N hW mesh base cells point test hq href hwhole profile Z]
  apply allocatedTranslatedReference_recenter_error <;> assumption

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

include hW hq hN hτ in
omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecenteredProfileMass_nonneg
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) :
    0 ≤ allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile y := by
  have hA : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hs := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hs.1 hs.2 (Nat.cast_pos.mpr S.positive) i
  unfold allocatedRecenteredProfileMass
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (selectedResidueCellWeight_nonneg _ _ _ _)
    (div_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hA.le))

include hq hN hτ in
theorem allocatedRecenteredProfileTerm_mesh_error
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (coarse E : ℝ)
    (hE : 0 ≤ E) (htest : ∀ v, ‖test v‖ ≤ 1)
    (hkernel : ∀ r v, v ∈ window →
      ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW mesh r v -
        allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW coarse r v‖ ≤ E)
    (y : fullTuple) :
    ‖allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y -
      allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile y‖ ≤
      E * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile y := by
  let H := trimmedSpatialRootScale τ N q
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t)
    (trimmedSpatialSlopeScale W τ N q t) S.value i
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let K := fun radius => allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW radius
    (principalResidueLabel modulus y)
  let recons := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  have hA : 0 < A := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim)
      (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
      (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).2 (Nat.cast_pos.mpr S.positive) i))
  have hcell (a : cells) :
      ‖(∑ v ∈ window, (K mesh v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v))) -
        ∑ v ∈ window, (K coarse v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v))‖ ≤
      E * ((∑ v ∈ window, ‖profile y (point (recons a.val v))‖) / A) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro v hv
    have hid : (K mesh v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v)) -
        (K coarse v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v)) =
      ((K mesh v - K coarse v) / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v)) := by ring
    rw [hid, norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hA.le]
    calc
      _ ≤ (E / A) * 1 * ‖profile y (point (recons a.val v))‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul (div_le_div_of_nonneg_right (hkernel _ v hv) hA.le)
          (htest _) (norm_nonneg _) (div_nonneg hE hA.le)
      _ = _ := by ring
  change ‖(∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window, (K mesh v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v))) -
    (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window, (K coarse v / (A : ℂ)) * test (recons a.val v) * profile y (point (recons a.val v)))‖ ≤
    E * ∑ a : cells, selectedResidueCellWeight q cells V a *
      ((∑ v ∈ window, ‖profile y (point (recons a.val v))‖) / A)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (selectedResidueCellWeight_nonneg q cells V a)]
  exact (mul_le_mul_of_nonneg_left (hcell a) (selectedResidueCellWeight_nonneg q cells V a)).trans_eq (by ring)

include hq hN hτ in

theorem allocatedRecenteredProfileTerm_mesh_error_law
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (coarse E : ℝ)
    (hE : 0 ≤ E) (htest : ∀ v, ‖test v‖ ≤ 1)
    (hkernel : ∀ r v, v ∈ window →
      ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW mesh r v -
        allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW coarse r v‖ ≤ E) :
    ‖law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) -
      law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile)‖ ≤
      E * law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile) := by
  have h := law.norm_complexMean_sub_le _ _
    (fun y => E * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile y)
    (fun y _ => allocatedRecenteredProfileTerm_mesh_error B U b S X modulus q wholeReference x
      hM selection hx N hW mesh base cells point test hq hN hτ profile coarse E hE htest hkernel y)
  simpa only [FiniteProbabilityWeights.mean_const_mul] using h

include hq hN hτ in

theorem allocatedRecenteredProfileTerm_remesh_law
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (Q : ℝ≥0) (hQ : 1 ≤ Q)
    (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hroot : ∀ g, |((x g none : ℤ) : ℝ)| ≤ 1 + W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hmesh : 0 < mesh) (coarse : ℝ) (hcoarse : 0 < coarse)
    (htest : ∀ v, ‖test v‖ ≤ 1) :
    ‖law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) -
      law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile)‖ ≤
      (Fintype.card X *
        (4 * (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (mesh + coarse)) *
        (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X) *
      law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile) := by
  have hκ : 0 ≤ 1 / (M : ℝ) := (one_div_pos.mpr (Nat.cast_pos.mpr hM)).le
  have hLip := anisotropicSpatialDensityLip_nonneg selection hκ
  have hCap := anisotropicSpatialDensityCap_nonneg selection hκ
  apply allocatedRecenteredProfileTerm_mesh_error_law B U b S X modulus q wholeReference x
    hM selection hx N hW mesh base cells point test hq hN hτ law profile coarse _
    (by positivity) htest
  exact allocatedResidueSpatialKernel_remesh B U b S x X hM selection hx modulus
    (trimmedSpatialRootScale τ N q) hW mesh Q hQ hratio hroot hperiod
    (fun t => (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1) hmesh coarse hcoarse

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

include hq hN hτ in
theorem allocatedRecenteredReference_mesh_error
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (coarse E Z : ℝ)
    (hE : 0 ≤ E) (hZ : 0 < Z) (htest : ∀ v, ‖test v‖ ≤ 1)
    (hkernel : ∀ r v, v ∈ window →
      ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW mesh r v -
        allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW coarse r v‖ ≤ E) :
    ‖(whole).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ) -
      (whole).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile) / (Z : ℂ)‖ ≤
      E * ((whole).mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile) / Z) := by
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  have h := (whole).norm_complexMean_sub_le _ _
    (fun y => E * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile y)
    (fun y _ => allocatedRecenteredProfileTerm_mesh_error B U b S X modulus q wholeReference x
      hM selection hx N hW mesh base cells point test hq hN hτ profile coarse E hE htest hkernel y)
  exact (div_le_div_of_nonneg_right h hZ.le).trans_eq (by rw [FiniteProbabilityWeights.mean_const_mul]; ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

noncomputable def allocatedRecenteredCoarseMesh (Q : ℝ≥0) (V ε : ℝ) : ℝ :=
  spatialTupleCoarseMesh (Fintype.card X)
    ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) * anisotropicSpatialDensityCap selection (1 / (M : ℝ)))
    V ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q)) ε

include hq hN hτ in
theorem allocatedRecenteredReference_coarse_comparison_law
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hroot : ∀ g, |((x g none : ℤ) : ℝ)| ≤ 1 + W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (Z V ε : ℝ) (hZ : 0 < Z) (hε : 0 < ε)
    (hMass : law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) / Z ≤ V) :
    let coarse := allocatedRecenteredCoarseMesh (M := M) X modulus selection Q V ε
    0 < coarse ∧ coarse ≤ 1 / 4 ∧
      ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
      ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
      ‖law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW fine base cells point test profile) / (Z : ℂ) -
        law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile) / (Z : ℂ)‖ ≤ ε := by
  intro coarse
  let cap := (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    anisotropicSpatialDensityCap selection (1 / (M : ℝ))
  let lip := (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q)
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hcap : 0 ≤ cap := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (anisotropicSpatialDensityCap_nonneg selection hκ)
  have hlip : 0 ≤ lip := mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (mul_nonneg (anisotropicSpatialDensityLip_nonneg selection hκ) Q.coe_nonneg)
  have hMass0 : 0 ≤ law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) / Z := by
    apply div_nonneg _ hZ.le
    exact law.mean_nonneg (fun y => allocatedRecenteredProfileMass_nonneg B U b S X modulus q
      wholeReference x N hW base cells point hq hN hτ profile y)
  have hcoarse := spatialTupleCoarseMesh_spec (Fintype.card X) hcap (hMass0.trans hMass) hlip hε
  refine ⟨hcoarse.1, hcoarse.2.1, ?_⟩
  intro fine hfine hle test htest
  have hcoarse0 : 0 < coarse := hcoarse.1
  let error := Fintype.card X * (8 * lip * coarse) * (1 + cap)^Fintype.card X
  have herror : 0 ≤ error := by dsimp only [error]; positivity
  have hH (t : X) : 0 < trimmedSpatialRootScale τ N q t :=
    (trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)).1
  have hkernel : ∀ r v, v ∈ window →
      ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW fine r v -
        allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
          (trimmedSpatialRootScale τ N q) hW coarse r v‖ ≤ error := by
    intro r v hv
    have h := allocatedResidueSpatialKernel_remesh B U b S x X hM selection hx modulus
      (trimmedSpatialRootScale τ N q) hW fine Q hQ hratio hroot hperiod hH hfine coarse hcoarse.1 r v hv
    apply h.trans
    change Fintype.card X * (4 * (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (fine + coarse)) *
      (1 + cap)^Fintype.card X ≤ error
    calc
      _ = Fintype.card X * (4 * lip * (fine + coarse)) * (1 + cap)^Fintype.card X := by
        dsimp only [lip]; ring
      _ ≤ Fintype.card X * (4 * lip * (coarse + coarse)) * (1 + cap)^Fintype.card X := by gcongr
      _ = error := by dsimp only [error]; ring
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  have he := allocatedRecenteredProfileTerm_mesh_error_law (ξ := ξ) B U b S X modulus q wholeReference x
    hM selection hx N hW fine base cells point test hq hN hτ law profile coarse error herror htest hkernel
  apply (div_le_div_of_nonneg_right he hZ.le).trans
  rw [mul_div_assoc]
  exact hcoarse.2.2 hcap le_rfl hlip le_rfl hMass0 hMass

include hq hN hτ in
theorem allocatedRecenteredReference_coarse_comparison
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hroot : ∀ g, |((x g none : ℤ) : ℝ)| ≤ 1 + W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (Z V ε : ℝ) (hZ : 0 < Z) (hε : 0 < ε)
    (hMass : (whole).mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) / Z ≤ V) :
    let coarse := allocatedRecenteredCoarseMesh (M := M) X modulus selection Q V ε
    0 < coarse ∧ coarse ≤ 1 / 4 ∧
      ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
      ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
      ‖(whole).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW fine base cells point test profile) / (Z : ℂ) -
        (whole).complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
          B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile) / (Z : ℂ)‖ ≤ ε  := by
  exact allocatedRecenteredReference_coarse_comparison_law B U b S X modulus q wholeReference x
    hM selection hx N hW base cells point hq hN hτ whole profile Q hQ hratio hroot hperiod Z V ε hZ hε hMass

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

noncomputable def allocatedEarlyRecenteredMesh {dim : ℕ} {G : Type*} [Fintype G]
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (M modulus : ℕ) (p E : ℝ) : ℝ :=
  allocatedRecenteredCoarseMesh (M := M) X modulus selection (allocatedPrimitiveRootRatio (Real.exp p))
    (Real.exp (coefficientErrorVolumeLog p + 4)) (Real.exp (-E))

noncomputable def allocatedEarlyCoarseInput {A : Type*} [Semiring A] (m dim : ℕ) (s : A) : A :=
  let R := s + (m + dim + 2 : ℕ)
  2 * R + R ^ 3 + anisotropicSpatialCapLog R + spatialLipschitzEnvelope R +
    coefficientErrorVolumeLog R + 8

theorem allocatedEarlyCoarseInput_bounds (m dim : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    let R := s + (m + dim + 2 : ℕ)
    let T := allocatedEarlyCoarseInput m dim s
    0 ≤ T ∧ R ≤ T ∧ R ^ 3 ≤ T ∧
      R ^ 3 + anisotropicSpatialCapLog R ≤ T ∧
      R ^ 3 + spatialLipschitzEnvelope R + R ≤ T ∧
      coefficientErrorVolumeLog R + 4 ≤ T := by
  intro R T
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcap := anisotropicSpatialCapLog_nonneg hR
  have hlip := (spatialCostEnvelopes_nonneg hR (le_refl (0 : ℝ))).2.2.2.2
  have hmass : 0 ≤ coefficientErrorVolumeLog R := by unfold coefficientErrorVolumeLog; positivity
  have hcube : 0 ≤ R ^ 3 := pow_nonneg hR _
  dsimp only [T, allocatedEarlyCoarseInput]
  change 0 ≤ 2 * R + R ^ 3 + anisotropicSpatialCapLog R + spatialLipschitzEnvelope R +
      coefficientErrorVolumeLog R + 8 ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hR, hcap, hlip, hmass, hcube]

theorem allocatedEarlyRecenteredMesh_partition_budget (m : ℕ) {dim : ℕ}
    {G : Type*} [Fintype G] (X : Type*) [Fintype X]
    (selection : Fin dim ↪ G) {M modulus : ℕ} {p E : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp p) (hmod : modulus ≤ M ^ (m + 1)) :
    let r := allocatedEarlyRecenteredMesh X selection M modulus p E
    let T := allocatedEarlyCoarseInput m dim (p + E)
    0 < r ∧ r ≤ 1 / 4 ∧ r⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog T) ∧
      allocatedSpatialCoefficientCap X selection M modulus r ≤
        Real.exp (coarseSpatialPartitionLog T) := by
  let s := p + E
  let R := s + (m + dim + 2 : ℕ)
  let T := allocatedEarlyCoarseInput m dim s
  have hs : 0 ≤ s := add_nonneg hp hE
  have hR2 : 2 ≤ R := by
    dsimp [R]
    push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hR : 0 ≤ R := by linarith only [hR2]
  obtain ⟨hT, hRT, hcubeT, hcapT, hlipT, hmassT⟩ := allocatedEarlyCoarseInput_bounds m dim hs
  change R ≤ T at hRT
  have hpR : p + 1 ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hE, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hpR' : p ≤ R := by linarith only [hpR]
  have hER : E ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hp, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hmR : ((m + 1 : ℕ) : ℝ) ≤ R := by
    dsimp [R]; push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) dim]
  have hnR : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ R := by
    simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    dsimp [R]; push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m]
  have hGR := hG.trans hpR'
  have hXR := hX.trans hpR'
  have hMR := hMP.trans (Real.exp_le_exp.mpr hpR')
  have hmodR := coefficientErrorPeriod_exp_sq hR hmR hMR hmod
  have hΓ : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) ≤ Real.exp (R ^ 3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hmodR (sq_nonneg R) _ hnR).trans_eq
      (congrArg Real.exp (by ring))
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hC0 := anisotropicSpatialDensityCap_nonneg selection hκ
  have hL0 := anisotropicSpatialDensityLip_nonneg selection hκ
  have hC := anisotropicSpatialDensityCap_exp_bound selection hR hM hMR hnR hGR
  have hfree : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ 2 * R := by
    have hcard := selectedColumn_card selection
    have hb : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ R :=
      (Nat.cast_le.mpr (by omega)).trans hGR
    linarith only [hb, hR]
  have hprofile := spatialProfileLog_le_fixedEnvelope _ _ hR hnR hfree
  have hL : anisotropicSpatialDensityLip selection (1 / (M : ℝ)) ≤
      Real.exp (spatialLipschitzEnvelope R) :=
    (anisotropicSpatialDensityLip_le_exp selection hR hM hMR hnR hGR).trans
      (Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprofile (by norm_num))))
  have hQ : (allocatedPrimitiveRootRatio (Real.exp p) : ℝ) ≤ Real.exp R := by
    rw [(allocatedPrimitiveRootRatio_bounds (Real.exp_pos p).le).1, add_comm]
    exact (one_add_le_exp_succ hp (le_refl (Real.exp p))).trans (Real.exp_le_exp.mpr hpR)
  have hcapInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * Real.exp (anisotropicSpatialCapLog R) := by gcongr
      _ = Real.exp (R ^ 3 + anisotropicSpatialCapLog R) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcapT
  have hlipInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * allocatedPrimitiveRootRatio (Real.exp p)) ≤
      Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * (Real.exp (spatialLipschitzEnvelope R) * Real.exp R) := by gcongr
      _ = Real.exp (R ^ 3 + spatialLipschitzEnvelope R + R) := by
        rw [← Real.exp_add, ← Real.exp_add, add_assoc]
      _ ≤ _ := Real.exp_le_exp.mpr hlipT
  have hmassLog : coefficientErrorVolumeLog p ≤ coefficientErrorVolumeLog R := by
    unfold coefficientErrorVolumeLog
    gcongr
  have hmassInput : Real.exp (coefficientErrorVolumeLog p + 4) ≤ Real.exp T :=
    Real.exp_le_exp.mpr ((add_le_add hmassLog le_rfl).trans hmassT)
  have hε : 0 < Real.exp (-E) := Real.exp_pos _
  have hεInput : (Real.exp (-E))⁻¹ ≤ Real.exp T := by
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (hER.trans hRT)
  have hsquare : R ^ 2 ≤ R ^ 3 := by
    calc
      R ^ 2 = R ^ 2 * 1 := (mul_one _).symm
      _ ≤ R ^ 2 * R := mul_le_mul_of_nonneg_left (by linarith only [hR2]) (sq_nonneg R)
      _ = R ^ 3 := by ring
  have hmodInput := hmodR.trans (Real.exp_le_exp.mpr (hsquare.trans hcubeT))
  have hΓInput := hΓ.trans (Real.exp_le_exp.mpr hcubeT)
  have hCInput := hC.trans (Real.exp_le_exp.mpr
    (show anisotropicSpatialCapLog R ≤ T from
      (le_add_of_nonneg_left (pow_nonneg hR 3)).trans hcapT))
  have hcap0 := mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus (α := ℝ)) (Fintype.card (Unit ⊕ Fin dim))) hC0
  have hlip0 := mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus (α := ℝ)) (Fintype.card (Unit ⊕ Fin dim)))
    (mul_nonneg hL0 (NNReal.coe_nonneg (allocatedPrimitiveRootRatio (Real.exp p))))
  have hspec := spatialTupleCoarseMesh_spec (Fintype.card X) hcap0
    (Real.exp_pos (coefficientErrorVolumeLog p + 4)).le hlip0 hε
  have hcost := spatialTupleCoarseMesh_partition_budget (Fintype.card X)
    (Fintype.card (Unit ⊕ Fin dim)) hcap0 (Real.exp_pos (coefficientErrorVolumeLog p + 4)).le hlip0
    (Nat.cast_nonneg _) hC0 hε hT (hXR.trans hRT) (hnR.trans hRT)
    hcapInput hmassInput hlipInput hεInput hmodInput hΓInput hCInput
  exact ⟨hspec.1, hspec.2.1, hcost.1, hcost.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedEarlyCoarseLog_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {s : ℝ}, 0 ≤ s →
      coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim s) ≤ (s + a) ^ a ∧
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim s) ≤ (s + a) ^ a := by
  let poly : Polynomial ℕ :=
    coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim Polynomial.X) +
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim Polynomial.X)
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro s hs
  have hsum : coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim s) +
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim s) ≤ (s + a) ^ a := by
    simpa [poly, allocatedEarlyCoarseInput, coarseSpatialReciprocalLog, coarseSpatialPartitionLog,
      spatialTupleToleranceLog, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
      anisotropicSpatialCapLog, coefficientErrorVolumeLog, Polynomial.eval₂_pow] using hpoly s hs
  obtain ⟨hinv, hpartition⟩ := coarseSpatialLogs_nonneg (allocatedEarlyCoarseInput_bounds m dim hs).1
  exact ⟨(le_add_of_nonneg_right hpartition).trans hsum,
    (le_add_of_nonneg_left hinv).trans hsum⟩

theorem exists_allocatedEarlyRecenteredMesh_budget (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G] (X : Type*) [Fintype X]
      (selection : Fin dim ↪ G) {M modulus : ℕ} {p E : ℝ},
      0 ≤ p → 0 ≤ E → (Fintype.card G : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      0 < M → (M : ℝ) ≤ Real.exp p → modulus ≤ M ^ (m + 1) →
      let r := allocatedEarlyRecenteredMesh X selection M modulus p E
      0 < r ∧ r ≤ 1 / 4 ∧ r⁻¹ ≤ Real.exp ((p + E + a) ^ a) ∧
        allocatedSpatialCoefficientCap X selection M modulus r ≤ Real.exp ((p + E + a) ^ a) := by
  obtain ⟨a, ha, hlogs⟩ := exists_allocatedEarlyCoarseLog_bound m dim
  refine ⟨a, ha, ?_⟩
  intro G _ X _ selection M modulus p E hp hE hG hX hM hMP hmod r
  have h := allocatedEarlyRecenteredMesh_partition_budget m X selection hp hE hG hX hM hMP hmod
  have hlog := hlogs (add_nonneg hp hE)
  exact ⟨h.1, h.2.1, h.2.2.1.trans (Real.exp_le_exp.mpr hlog.1),
    h.2.2.2.trans (Real.exp_le_exp.mpr hlog.2)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

include hq hN hτ in
theorem allocatedRecentered_early_coarse_source_law
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p) (hmodulus : modulus ≤ M ^ (m + 1))
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hmass : law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) ≤
        coarseReferenceMassConstant dim X W S.value) :
    let coarse := allocatedEarlyRecenteredMesh X selection M modulus p E
    let T := allocatedEarlyCoarseInput m dim (p + E)
    0 < coarse ∧ coarse ≤ 1 / 4 ∧ coarse⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog T) ∧
      allocatedSpatialCoefficientCap X selection M modulus coarse ≤ Real.exp (coarseSpatialPartitionLog T) ∧
    ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ κ : ℝ,
      κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW fine base cells point test profile)).re →
      κ - Real.exp (-E) ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile)).re := by
  intro coarse T
  obtain ⟨hc, hc1, hci, hcost⟩ := allocatedEarlyRecenteredMesh_partition_budget m X selection
    hp hE hG hX hM hMP hmodulus
  refine ⟨hc, hc1, hci, hcost, ?_⟩
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hratio : (1 + W) / (S.value : ℝ) ≤ allocatedPrimitiveRootRatio (Real.exp p) := by
    rw [(allocatedPrimitiveRootRatio_bounds (Real.exp_pos p).le).1]
    apply (div_le_iff₀ hS).mpr
    have hv := mul_le_mul_of_nonneg_right hvars hS.le
    nlinarith only [hWscale, hv, hS1]
  obtain ⟨y, _⟩ := law.exists_weight_pos
  have hroot (g : G) : |((x g none : ℤ) : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y (.inl g)).trans hbudget
    change |(((0 : ℤ) + (x g none : ℤ) : ℤ) : ℝ)| ≤ W at h
    simp only [zero_add] at h
    linarith only [h]
  have hMass := hmass.trans (coarseReferenceMassConstant_exp_bound dim X hp hdim hX hS1 hW hvars hWscale)
  have hcompare := allocatedRecenteredReference_coarse_comparison_law (ξ := ξ) B U b S X modulus q
    wholeReference x hM selection hx N hW base cells point hq hN hτ law profile
    (allocatedPrimitiveRootRatio (Real.exp p)) (allocatedPrimitiveRootRatio_bounds (Real.exp_pos p).le).2.1
    hratio hroot hperiod 1 (Real.exp (coefficientErrorVolumeLog p + 4)) (Real.exp (-E))
    (by norm_num) (Real.exp_pos _) (by simpa only [div_one] using hMass)
  intro fine hfine hle test htest κ hsource
  have he := hcompare.2.2 fine hfine hle test htest
  simp only [Complex.ofReal_one, div_one] at he
  have hre := (Complex.re_le_norm _).trans he
  rw [Complex.sub_re] at hre
  change _ - (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile)).re ≤ _ at hre
  linarith only [hsource, hre]

end Erdos3.VectorPolynomial

end

end OAI
