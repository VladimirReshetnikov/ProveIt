import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalExponentialCover

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

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedNarrowTrimmed_recentered_profile_error
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple)
    (hwhole : principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) =
      principalResidueLabel refined y)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg) (hcap : ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 0 < Z) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y
    let dirs := allocatedPhysicalCubeDirections B U b S x y
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences root dirs base z) *
          profile y (point (physicalCubeRootDifferences root dirs base z)))) / (Z : ℂ) -
      allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z + spatialError * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile y / Z := by
  intro V hV root dirs
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hE : 0 ≤ spatialError := by
    have he := anisotropicSpatialError_nonneg selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M
      hκ.le (zero_le_one.trans hC₀) hρ.le hξ.le
    have hl := anisotropicSpatialDensityLip_nonneg selection hκ.le
    have hc := anisotropicSpatialDensityCap_nonneg selection hκ.le
    unfold allocatedTupleSpatialError
    dsimp only
    positivity
  have hA : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hp := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hp.1 hp.2 (Nat.cast_pos.mpr S.positive) i
  have he := allocatedNarrowTrimmed_whole_reference_mass_test B U b S (fun _ => 0) x y
    (wholeReference (principalResidueLabel refined y)) selection N q hN hq hW hτ hκ hρ hx
    hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 modulus hperiod refined
    (stride_mul_dvd_residueRefinedPeriod modulus q) hwhole.symm hδ hρshift hρmove hmeshpos base cells hmass
    (fun v => test v * profile y (point v)) hCg
    (fun v => by rw [norm_mul]; exact (mul_le_mul_of_nonneg_right (htest v) (norm_nonneg _)).trans (by simpa using hcap v)) hZ
  dsimp only at he
  have hcoarse := principalResidueLabel_eq_of_dvd _ _
    (show modulus ∣ residueRefinedPeriod modulus q from ⟨∏ t, q t, rfl⟩) hwhole
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  have hcompare : ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences root dirs base z) *
          profile y (point (physicalCubeRootDifferences root dirs base z)))) / (Z : ℂ) -
      allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile y / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a * ((spatialError / A) *
          ∑ v ∈ window, ‖test (reconstruct a.val v) * profile y (point (reconstruct a.val v))‖)) / Z := by
    simpa only [allocatedRecenteredProfileTerm, allocatedWholeResidueReconstruction,
      allocatedResidueSpatialKernel, principalSpatialColumns_residue, hcoarse,
      allocatedTupleSpatialError, mul_assoc, A, reconstruct] using he
  refine hcompare.trans (add_le_add le_rfl ?_)
  apply div_le_div_of_nonneg_right _ hZ.le
  unfold allocatedRecenteredProfileMass
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [mul_left_comm spatialError]
  apply mul_le_mul_of_nonneg_left _ (selectedResidueCellWeight_nonneg _ _ _ _)
  change spatialError / _ * _ ≤ spatialError * (_ / _)
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hA.le
  apply mul_le_mul_of_nonneg_left _ hE
  apply Finset.sum_le_sum
  intro v _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (htest _) (norm_nonneg _)).trans_eq (one_mul _)

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
theorem allocatedNarrowTrimmed_recentered_profile_error_law
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, law.weight y ≠ 0 → ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 0 < Z) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          profile y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)))
    ‖law.complexMean projected / (Z : ℂ) -
      law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z + spatialError * law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile) / Z := by
  intro V hV projected
  let recentered := allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile
  let mass := allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
    B U b S X modulus q wholeReference x N base cells point profile
  have he := law.norm_complexMean_sub_le (fun y => projected y / (Z : ℂ))
    (fun y => recentered y / (Z : ℂ)) (fun y => Cg * boundaryError / Z + spatialError * mass y / Z)
    (fun y hy => allocatedNarrowTrimmed_recentered_profile_error B U b S X modulus q wholeReference
      x hM selection hx N hW mesh base cells point test hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1
      hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos hmass htest profile y (hwhole y hy) hCg (hcap y hy) hZ)
  rw [FiniteProbabilityWeights.complexMean_div_const, FiniteProbabilityWeights.complexMean_div_const,
    FiniteProbabilityWeights.mean_add, FiniteProbabilityWeights.mean_const] at he
  have hm : law.mean (fun y => spatialError * mass y / Z) = spatialError * law.mean mass / Z := by
    simp only [FiniteProbabilityWeights.mean, mul_div_assoc, Finset.sum_div]
    rw [Finset.mul_sum]
    congr 1
    funext y
    ring
  rw [hm] at he
  exact he

include hN hq hτ hξ hW hmass in
omit [DecidableEq G] [NeZero modulus] in
theorem allocatedRecenteredProfileMass_le_of_window_law
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (hwindow : ∀ y, law.weight y ≠ 0 → ∀ a : cells,
      (∑ v ∈ window, ‖profile y (point (allocatedWholeResidueReconstruction B U b S X modulus q
        wholeReference x base (principalResidueLabel refined y) a.val v))‖) ≤
        (4 * (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X)) *
          (∏ t, ∏ _i : Unit ⊕ Fin dim, trimmedSpatialRootScale τ N q t)) :
    law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) ≤
      coarseReferenceMassConstant dim X W S.value := by
  rw [← law.mean_const (coarseReferenceMassConstant dim X W S.value)]
  apply law.mean_mono_on_support
  intro y hy
  let y₀ := wholeReference (principalResidueLabel refined y)
  have hA : 0 < ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
      (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i := by
    apply Finset.prod_pos
    intro t _
    apply Finset.prod_pos
    intro i _
    have hp := trimmedSpatial_scales_pos hW hτ N q t (hN t) (hq t)
    exact physicalSpatialOutputScale_pos (Fin dim) hp.1 hp.2 (Nat.cast_pos.mpr S.positive) i
  have he := coarse_reference_density_spatial_error q cells
    (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
    (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN) hmass
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀)
    (allocatedPhysicalCubeDirections B U b S x y₀) base
    (trimmedSpatialRootScale τ N q) (trimmedSpatialSlopeScale W τ N q)
    (Nat.cast_pos.mpr S.positive).ne' (trimmedSpatial_scale_ratio hW N q) hA
    point (fun z => ‖profile y z‖) (fun _ => norm_nonneg _) (fun _ => (1 : ℂ))
    (fun _ => by simp) (E := 1) (by norm_num) (hwindow y hy)
  simpa only [allocatedRecenteredProfileMass, allocatedWholeResidueReconstruction,
    norm_one, one_mul, one_div_mul_eq_div, y₀] using he

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
theorem allocatedNarrowTrimmed_recentered_source_law
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, law.weight y ≠ 0 → ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 1 / 2 ≤ Z) {target κ : ℝ}
    (hmassBound : law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) ≤
        coarseReferenceMassConstant dim X W S.value)
    (hboundary : Cg * boundaryError ≤ normalizedSpatialShare target / 2)
    (hsite : spatialError * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          profile y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)))
    κ ≤ (law.complexMean projected / (Z : ℂ)).re →
    Z * (κ - Real.exp (-target)) ≤
      (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)).re := by
  intro V hV projected hsource
  have hZpos : 0 < Z := by linarith
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hE : 0 ≤ spatialError := by
    have he := anisotropicSpatialError_nonneg selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M
      hκ.le (zero_le_one.trans hC₀) hρ.le hξ.le
    have hl := anisotropicSpatialDensityLip_nonneg selection hκ.le
    have hc := anisotropicSpatialDensityCap_nonneg selection hκ.le
    unfold allocatedTupleSpatialError
    dsimp only
    positivity
  have he := allocatedNarrowTrimmed_recentered_profile_error_law B U b S X modulus q wholeReference
    x hM selection hx N hW mesh base cells point test hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos hmass htest law hwhole profile hCg hcap hZpos
  have hb : Cg * boundaryError / Z ≤ normalizedSpatialShare target := by
    apply (div_le_iff₀ hZpos).mpr
    have hp : 0 < normalizedSpatialShare target := Real.exp_pos _
    nlinarith
  have hs : spatialError * law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) / Z ≤ normalizedSpatialShare target := by
    apply (div_le_iff₀ hZpos).mpr
    have hp : 0 < normalizedSpatialShare target := Real.exp_pos _
    have hh := (mul_le_mul_of_nonneg_left hmassBound hE).trans hsite
    nlinarith
  have hsmall : 2 * normalizedSpatialShare target ≤ Real.exp (-target) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-(target + 2)) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hnorm := he.trans (show _ ≤ Real.exp (-target) by linarith only [hb, hs, hsmall])
  have hre := (Complex.re_le_norm _).trans hnorm
  rw [Complex.sub_re] at hre
  have hout : κ - Real.exp (-target) ≤
      (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)).re := by
    linarith only [hsource, hre]
  rw [Complex.div_ofReal_re] at hout
  exact (mul_comm Z _).le.trans ((le_div_iff₀ hZpos).mp hout)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
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

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
theorem allocatedNarrowTrimmed_early_coarse_source_law
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, law.weight y ≠ 0 → ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 1 / 2 ≤ Z) {target κ : ℝ}
    (hmassBound : law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) ≤
        coarseReferenceMassConstant dim X W S.value)
    (hboundary : Cg * boundaryError ≤ normalizedSpatialShare target / 2)
    (hsite : spatialError * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2)
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p) (hmodulus : modulus ≤ M ^ (m + 1))
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hmeshCoarse : mesh ≤ allocatedEarlyRecenteredMesh X selection M modulus p E) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          profile y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)))
    κ ≤ (law.complexMean projected / (Z : ℂ)).re →
    Z * (κ - Real.exp (-target)) - Real.exp (-E) ≤
      (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW
          (allocatedEarlyRecenteredMesh X selection M modulus p E) base cells point test profile)).re := by
  intro V hV projected hsource
  have hfine := allocatedNarrowTrimmed_recentered_source_law B U b S X modulus q wholeReference
    x hM selection hx N hW mesh base cells point test hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos hmass htest law hwhole profile hCg hcap
    hZ hmassBound hboundary hsite hsource
  obtain ⟨_, _, _, _, htransfer⟩ := allocatedRecentered_early_coarse_source_law (ξ := ξ)
    B U b S X modulus q wholeReference x hM selection hx N hW base cells point hq hN hτ law profile
    hp hE hG hX hdim hMP hmodulus hvars hbudget hWscale hperiod hmassBound
  exact htransfer mesh hmeshpos hmeshCoarse test htest (Z * (κ - Real.exp (-target))) hfine

end Erdos3.VectorPolynomial

end

end OAI
