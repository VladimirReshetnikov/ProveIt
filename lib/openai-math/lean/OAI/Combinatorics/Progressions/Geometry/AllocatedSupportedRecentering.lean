import OAI.Combinatorics.Progressions.Estimates.AllocatedSlicedCoarseSource

namespace OAI

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

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
variable (href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
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

include hq hN hτ href hQ hratio hbudget hperiod hmesh hε hmargin hsize htest in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedTranslatedProfileTerm_recenter_error_at
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple)
    (hwhole : principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) =
      principalResidueLabel refined y) :
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
    have hnormalized := allocatedResidueReferenceShift_normalized_at B U b S X modulus q reference wholeReference x
      hq href H hH hε hsize y hwhole a.val
    have hlattice := (allocatedResidueReferenceShift_spec_at B U b S X modulus q reference wholeReference x
      hq href base y hwhole a.val).1
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

include hq hN hτ href hQ hratio hbudget hperiod hmesh hε hmargin hsize htest in
theorem allocatedResidueWeightedReference_recenter_error_support
    (hwhole : ∀ y : fullTuple, (whole).weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) =
        principalResidueLabel refined y)
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
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  apply div_le_div_of_nonneg_right _ hZ.le
  have h := (whole).norm_complexMean_sub_le
    (allocatedResidueWeightedProfileTerm (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile)
    (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)
    (fun y => shiftError * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile y)
    (fun y hy => by
      have hwy := hwhole y hy
      rw [allocatedResidueWeightedProfileTerm_translate_at B U b S X modulus q reference wholeReference x
        hM selection hx N hW mesh base cells point test hq href profile y hwy]
      apply allocatedTranslatedProfileTerm_recenter_error_at <;> assumption)
  simpa only [FiniteProbabilityWeights.mean_const_mul] using h

end Erdos3.VectorPolynomial

end

end OAI
