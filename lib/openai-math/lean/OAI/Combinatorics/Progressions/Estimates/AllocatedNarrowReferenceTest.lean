import OAI.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

omit [DecidableEq α] in
theorem allocatedTrimmedSpatial_whole_reference_window
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    {X : Type*} [Fintype X] (N q : X → ℕ)
    (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (r : Option vars × X → ℤ) (hr : ∀ k d, |(r (k,d) : ℝ)| ≤ q d)
    (period modulus : ℕ) (hdiv : ∀ d, q d * period ∣ modulus)
    (hlabel : principalResidueLabel modulus y = principalResidueLabel modulus y₀)
    (hsmall : ∀ d, 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ trimmedSpatialRootScale τ N q d)
    (v : X → (Unit ⊕ α) → ℤ)
    (hv : v ∈ centeredPhysicalCubeWindow
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (residueProfileWidth q (trimmedSpatialWidths (K := vars) W τ N))) :
    v + physicalResidueOffsetShift
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeRoot B U basis S c x y₀)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (allocatedPhysicalCubeDirections B U basis S x y₀) r q ∈
      spatialWindow (trimmedSpatialRootScale τ N q) 4 := by
  let H := trimmedSpatialRootScale τ N q
  let shift := physicalResidueOffsetShift
    (allocatedPhysicalCubeRoot B U basis S c x y)
    (allocatedPhysicalCubeRoot B U basis S c x y₀)
    (allocatedPhysicalCubeDirections B U basis S x y)
    (allocatedPhysicalCubeDirections B U basis S x y₀) r q
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hbound := (allocatedPhysicalResidue_whole_offset_shift B U basis S c x y y₀
    (0 : X → ℤ) r q hq period modulus hdiv hlabel hr).2.2
  have hs : shift ∈ spatialWindow H 1 := by
    have hcoord : ∀ d i, |(shift d i : ℝ)| ≤ H d * (1/2) := by
      intro d i
      have h := hbound d i
      have hh := hsmall d
      change |(shift d i : ℝ)| ≤ _ at h
      change 2 * _ ≤ H d at hh
      linarith
    have h := spatialWindow_of_coordinate_bound H (fun d => (hH d).le)
      (by norm_num : (0 : ℝ) ≤ 1/2) shift hcoord
    norm_num only at h
    exact h
  have hv' : v ∈ spatialWindow H 3 :=
    (mem_spatialWindow_scaled_iff H hH 3 v).mpr
      (allocatedTrimmedSpatial_window_bound B U basis S c x y
        N q hN hq hW hτ hbudget v hv)
  have h := spatialWindow_add H hv' hs
  norm_num only at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "root₀" => allocatedPhysicalCubeRoot B U basis S c x y₀
local notation "dirs₀" => allocatedPhysicalCubeDirections B U basis S x y₀

theorem allocatedNarrowTrimmed_whole_reference_mass_test (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ δ r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ (ξ * τ) * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (refined : ℕ) (hdiv : ∀ d, q d * modulus ∣ refined)
    (hlabel : principalResidueLabel refined y = principalResidueLabel refined y₀)
    (hδ : 0 ≤ δ)
    (hρshift : 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ ρ)
    (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c) ≤ δ * ρ)
    (hr : 0 < r) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option vars) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths W τ ξ N) z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {Cφ Z : ℝ}
    (hCφ : 0 ≤ Cφ) (hφ : ∀ v, ‖φ v‖ ≤ Cφ) (hZ : 0 < Z) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let _Q := residueProfileWidth q V
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun v : X → (Unit ⊕ α) → ℤ => ∏ d,
      spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix refcols modulus))) modulus f (H d) 4 r (v d)
    let A := ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i
    let E₀ := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    let E₁ := E₀ + G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * δ
    let E := Fintype.card X * (E₁ + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
      (1 + G₀ * anisotropicSpatialDensityCap selection κ + E₁) ^ Fintype.card X
    let window := spatialWindow H 4
    let F := fun a : cells => physicalResidueReconstruction root₀ dirs₀ base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root dirs base z)) / (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      Cφ * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option vars × X) / ρ) / Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a *
          ((E / A) * ∑ v ∈ window, ‖φ (F a v)‖)) / Z := by
  classical
  intro H T V hV Q hpivot f ψ A E₀ G₀ E₁ E window F
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hT (d) : 0 < T d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2
  have hshiftSmall (d) : 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ H d :=
    hρshift.trans (narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N q d (hN d) (hq d) (hsize d)).1
  have hmoveSmall (d) : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c) ≤ δ * H d :=
    hρmove.trans (mul_le_mul_of_nonneg_left
      (narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N q d (hN d) (hq d) (hsize d)).1 hδ)
  have hA : 0 < A := Finset.prod_pos (fun d _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos α (hH d) (hT d) (Nat.cast_pos.mpr S.positive) i))
  have hCR (d) : integerResidueMatrix cols (q d * modulus) =
      integerResidueMatrix refcols (q d * modulus) := by
    apply integerResidueMatrix_reduce _ _ (hdiv d)
    rw [principalSpatialColumns_residue, principalSpatialColumns_residue, hlabel]
  have hphysical (d) : integerResidueMatrix (physicalCubeCoefficient root dirs) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ dirs₀) (q d * modulus) :=
    integerResidueMatrix_reduce _ _ (hdiv d)
      (allocatedPhysicalCube_residue_of_whole_label B U basis S c x y y₀ refined hlabel)
  have hrep (a : cells) (k) (d) :
      |(boundedColumnResidueRepresentative q a.val (k,d) : ℝ)| ≤ q d := by
    have h := boundedColumnResidueRepresentative_bounds q hq a.val (k,d)
    rw [abs_of_nonneg (by exact_mod_cast h.1 :
      (0 : ℝ) ≤ boundedColumnResidueRepresentative q a.val (k,d))]
    exact_mod_cast h.2.le
  have hwindow (a : cells) (v) (hv : v ∈ centeredPhysicalCubeWindow root dirs Q) :
      v + physicalResidueOffsetShift root root₀ dirs dirs₀
        (boundedColumnResidueRepresentative q a.val) q ∈ window :=
    allocatedTrimmedSpatial_whole_reference_window B U basis S c x y y₀ N q hN hq hW hτ hbudget
      (boundedColumnResidueRepresentative q a.val) (hrep a) modulus refined hdiv hlabel hshiftSmall v
        (narrowTrimmedSpatial_window_subset root dirs hW hτ hξ1 N q hN hv)
  have he (a : cells) (v) (hv : v ∈ window) :
      ‖((A * (((smoothProductPMF Q (residueProfileWidth_pos q V hq hV)).map
        (centeredPhysicalCubeMap root dirs))
          (v - physicalResidueOffsetShift root root₀ dirs dirs₀
            (boundedColumnResidueRepresentative q a.val) q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E :=
    allocatedNarrowTrimmed_shifted_vector_site_error B U basis S c x y y₀ selection N q hN hq
      hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh
      modulus hperiod (boundedColumnResidueRepresentative q a.val) (hrep a) hCR hδ
      (fun d i => (allocatedPrincipalColumns_difference_sum_bound B U basis S c x y y₀ i).trans (hmoveSmall d))
      (by norm_num : (0 : ℝ) < 4) hr v ((mem_spatialWindow_scaled_iff H hH 4 v).mp hv)
  have hwidth (z : Option vars × X) : ρ ≤ residueProfileWidth q V z :=
    narrowTrimmedSpatial_residue_width_lower hW hτ hξ1 hρ.le N q hN hq hsize z
  have hrec := physicalSelectedResidue_width_recenter root dirs base q hq cells V hV hmass
    hρ8 hwidth φ hCφ hφ hZ
  have hsite := physicalCenteredResidueMixture_reference_error root root₀ dirs dirs₀ base q hq modulus hphysical
    cells V hV window hwindow ψ φ hA hZ he
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hrec hsite)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (w w₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "y" => principalAxisJoin grid u w
local notation "y₀" => principalAxisJoin grid u w₀

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y
local notation "root₀" => allocatedPhysicalCubeRoot B U basis S c x y₀
local notation "dirs₀" => allocatedPhysicalCubeDirections B U basis S x y₀

theorem allocatedNarrowTrimmed_reference_mass_test (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ δ r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ (ξ * τ) * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (refined : ℕ) (hdiv : ∀ d, q d * modulus ∣ refined)
    (hlabel : principalResidueLabel refined w = principalResidueLabel refined w₀)
    (hδ : 0 ≤ δ)
    (hρshift : 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ ρ)
    (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c) ≤ δ * ρ)
    (hr : 0 < r) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option vars) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths W τ ξ N) z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {Cφ Z : ℝ}
    (hCφ : 0 ≤ Cφ) (hφ : ∀ v, ‖φ v‖ ≤ Cφ) (hZ : 0 < Z) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let _Q := residueProfileWidth q V
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun v : X → (Unit ⊕ α) → ℤ => ∏ d,
      spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix refcols modulus))) modulus f (H d) 4 r (v d)
    let A := ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i
    let E₀ := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    let E₁ := E₀ + G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * δ
    let E := Fintype.card X * (E₁ + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
      (1 + G₀ * anisotropicSpatialDensityCap selection κ + E₁) ^ Fintype.card X
    let window := spatialWindow H 4
    let F := fun a : cells => physicalResidueReconstruction root₀ dirs₀ base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root dirs base z)) / (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      Cφ * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option vars × X) / ρ) / Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a *
          ((E / A) * ∑ v ∈ window, ‖φ (F a v)‖)) / Z := by
  classical
  exact allocatedNarrowTrimmed_whole_reference_mass_test B U basis S c x y y₀
    selection N q hN hq hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh
    hρ8 modulus hperiod refined hdiv
    (by rw [principalResidueLabel_join, principalResidueLabel_join, hlabel])
    hδ hρshift hρmove hr base cells hmass φ hCφ hφ hZ

end Erdos3.VectorPolynomial

end

end OAI
