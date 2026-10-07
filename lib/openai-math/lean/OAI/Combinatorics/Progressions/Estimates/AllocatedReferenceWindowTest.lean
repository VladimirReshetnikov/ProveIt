import OAI.Combinatorics.Progressions.Geometry.SpatialShiftedWindowError
import OAI.Combinatorics.Progressions.Lattices.AllocatedTrimmedResidueTest
import OAI.Combinatorics.Progressions.Lattices.AllocatedWholeResidueShift
import OAI.Combinatorics.Progressions.Lattices.ShiftedResidueSiteComparison

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem smoothPhysicalResidue_window_expectation {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ)
    (Q : Option K × X → ℝ) (hQ : ∀ z, 0 < Q z)
    (window : Finset (X → (Unit ⊕ α) → ℤ))
    (hwindow : centeredPhysicalCubeWindow root D Q ⊆ window)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) :
    (∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
      φ (physicalCubeResidueCoordinates root D base residue q z)) =
    ∑ v ∈ window, (((smoothProductPMF Q hQ).map (centeredPhysicalCubeMap root D) v).toReal : ℂ) *
      φ (physicalResidueReconstruction root D base residue q v) := by
  classical
  have h := pmf_image_finite_expectation (smoothProductPMF Q hQ)
    (rectangularWeightIndices 0 Q 1) (smoothProductPMF_toReal_zero_off Q hQ)
    (centeredPhysicalCubeMap root D) window
    (fun z hz => hwindow (centeredPhysicalCubeMap_mem_window root D Q z hz))
    (fun v => φ (physicalResidueReconstruction root D base residue q v))
  simpa only [physicalResidueReconstruction_centered] using h

theorem physicalCenteredResidueMixture_window_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d)
    (cells : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (window : Finset (X → (Unit ⊕ α) → ℤ))
    (hwindow : centeredPhysicalCubeWindow root D (residueProfileWidth q V) ⊆ window)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E Z : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (he : ∀ v ∈ window,
      ‖((A * (((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV)).map (centeredPhysicalCubeMap root D)) v).toReal : ℝ) : ℂ) -
        ψ v‖ ≤ E) :
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let F := fun a : cells => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
          φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q a.val) q z)) /
          (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      (∑ a : cells, selectedResidueCellWeight q cells V a *
        ((E / A) * ∑ v ∈ window, ‖φ (F a v)‖)) / Z := by
  classical
  intro Q hQ F
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  apply div_le_div_of_nonneg_right _ hZ.le
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (selectedResidueCellWeight_nonneg q cells V a)]
  apply mul_le_mul_of_nonneg_left _ (selectedResidueCellWeight_nonneg q cells V a)
  have h := pmf_image_finite_test_error (smoothProductPMF Q hQ)
    (rectangularWeightIndices 0 Q 1) (smoothProductPMF_toReal_zero_off Q hQ)
    (centeredPhysicalCubeMap root D) window
    (fun z hz => hwindow (centeredPhysicalCubeMap_mem_window root D Q z hz)) ψ
    (fun v => φ (F a v)) hA he
  simpa only [F, physicalResidueReconstruction_centered] using h

theorem physicalSelectedResidue_window_site_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d)
    (cells : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells V z)
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (window : Finset (X → (Unit ⊕ α) → ℤ))
    (hwindow : centeredPhysicalCubeWindow root D (residueProfileWidth q V) ⊆ window)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E Z B : ℝ}
    (hA : 0 < A) (hZ : 0 < Z) (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B)
    (he : ∀ v ∈ window,
      ‖((A * (((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV)).map (centeredPhysicalCubeMap root D)) v).toReal : ℝ) : ℂ) -
        ψ v‖ ≤ E) :
    let F := fun a : cells => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : Option K × X, (q z.2 : ℝ) / V z)) / Z +
      (∑ a : cells, selectedResidueCellWeight q cells V a *
        ((E / A) * ∑ v ∈ window, ‖φ (F a v)‖)) / Z := by
  intro F
  have hrec := physicalSelectedResidue_recenter_test root D base q hq cells V hV hmass hlarge φ hB hφ hZ
  have hsite := physicalCenteredResidueMixture_window_error root D base q hq cells V hV window hwindow ψ φ hA hZ he
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hrec hsite)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem canonicalVectorSpatialSiteApprox_shift_error {D I J N : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N]
    (s : I ↪ J) (root : J → ℤ) (M : Matrix I J ℤ)
    (hpivot : (selectedSpatialPivot root M s).det ≠ 0)
    (C R : D → Matrix (Unit ⊕ I) N ℤ) (H T : D → ℝ)
    {W L κ E δ b r : ℝ} (hH : ∀ d, 0 < H d) (hT : ∀ d, 0 < T d)
    (hW : 0 ≤ W) (hL : 0 < L) (hL1 : 1 ≤ L) (hκ : 0 < κ)
    (hscale : ∀ d, H d = (1 + W) * T d)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) (hM : ∀ i j, |(M i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (M i (s j) : ℝ) / L)).det|)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root M s) (selectedSpatialFreeColumns root M s))
    (q : D → ℕ) (hq : ∀ d, 0 < q d) (residue : D → N → ℤ)
    (hresidue : ∀ d j, |(residue d j : ℝ)| ≤ q d)
    (hCR : ∀ d, integerResidueMatrix (C d) (q d * m) = integerResidueMatrix (R d) (q d * m))
    (hδ : 0 ≤ δ)
    (hmove : ∀ d i, (∑ j, |((C d i j - R d i j : ℤ) : ℝ)|) ≤ δ * H d)
    (mass : D → ((Unit ⊕ I) → ℤ) → ℝ) (hE : 0 ≤ E) (hb : 0 < b) (hr : 0 < r)
    (hmass : ∀ d v, |mass d v -
      maskedIntegerImageDensity (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (C d))
        (physicalSpatialOutputScale I (H d) (T d) L)
        (anisotropicSpatialKernelDensity s root M hpivot (H d) (T d) L (hH d) (hT d) hL) v| ≤ E)
    (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b) :
    let G := (m : ℝ) ^ Fintype.card (Unit ⊕ I)
    let f := canonicalSpatialSiteDensity s root M hpivot W L hW hL
    let shift := fun d => residueMatrixShift (C d) (R d) (q d) (residue d)
    let E' := E + G * (anisotropicSpatialDensityLip s κ * (1 + W)) * δ
    ‖((∏ d, mass d (v d - shift d) : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (liftResidueMatrix (integerResidueMatrix (R d) m)))
        m f (H d) b r (v d)‖ ≤
      Fintype.card D * (E' + 4 * G * (anisotropicSpatialDensityLip s κ * (1 + W)) * r) *
        (1 + G * anisotropicSpatialDensityCap s κ + E') ^ Fintype.card D := by
  intro G f shift E'
  have hpfull (d : D) : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (R d)) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  have hi (d : D) :
      ((pivotFullImage (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (R d))).toAddSubgroup.index : ℝ) ≤ G := by
    dsimp only [G]
    exact_mod_cast residueLatticeImage_index_le _ m (hpfull d)
  have hreg := canonicalSpatialSiteDensity_bounds s root M hpivot hW hL hL1 hκ hroot hM hminor
  have he (d : D) (w : (Unit ⊕ I) → ℤ) : |mass d w -
      maskedIntegerImageDensity (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (C d)) (fun _ => H d) f w| ≤ E := by
    have h := hmass d w
    rw [anisotropicSpatial_mask_canonical s root M hpivot _ (hH d) (hT d) hW hL (hscale d)] at h
    exact h
  have h := refinedResidue_shifted_site_error _ _ C R m hp q hq residue hresidue hCR
    (fun _ => f) (fun _ => hreg.2) H hH mass (by positivity)
    (anisotropicSpatialDensityCap_nonneg s hκ.le) hE hδ hb hr hi
    (fun _ => hreg.1) he hmove v hv
  have hid (d : D) := congrFun (spatialSiteApprox_eq_residue (selectedSpatialPivot root M s)
    (selectedSpatialFreeColumns root M s) (R d) m hp f (H d) b r) (v d)
  simpa only [hid, NNReal.coe_mul,
    Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg s hκ.le),
    Real.coe_toNNReal _ (by linarith : 0 ≤ 1 + W)] using h

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem smoothPhysicalResidue_reference_window_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (modulus : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * modulus))
    (Q : Option K × X → ℝ) (hQ : ∀ z, 0 < Q z)
    (window : Finset (X → (Unit ⊕ α) → ℤ))
    (hwindow : ∀ v ∈ centeredPhysicalCubeWindow root D Q,
      v + physicalResidueOffsetShift root root₀ D D₀ r q ∈ window)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ v ∈ window,
      ‖((A * (((smoothProductPMF Q hQ).map (centeredPhysicalCubeMap root D))
        (v - physicalResidueOffsetShift root root₀ D D₀ r q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E) :
    ‖(∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
        φ (physicalCubeResidueCoordinates root D base r q z)) -
      ∑ v ∈ window, (ψ v / (A : ℂ)) *
        φ (physicalResidueReconstruction root₀ D₀ base r q v)‖ ≤
      (E/A) * ∑ v ∈ window, ‖φ (physicalResidueReconstruction root₀ D₀ base r q v)‖ := by
  classical
  have h := pmf_image_shifted_finite_test_error (smoothProductPMF Q hQ)
    (rectangularWeightIndices 0 Q 1) (smoothProductPMF_toReal_zero_off Q hQ)
    (centeredPhysicalCubeMap root D) (physicalResidueOffsetShift root root₀ D D₀ r q)
    window (fun z hz => hwindow _ (centeredPhysicalCubeMap_mem_window root D Q z hz)) ψ
    (fun v => φ (physicalResidueReconstruction root₀ D₀ base r q v)) hA he
  simpa only [← physicalResidueReconstruction_offset_shift root root₀ D D₀ base r q hq modulus hres,
    physicalResidueReconstruction_centered] using h

theorem physicalCenteredResidueMixture_reference_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d) (modulus : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * modulus))
    (cells : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (window : Finset (X → (Unit ⊕ α) → ℤ))
    (hwindow : ∀ a : cells, ∀ v ∈ centeredPhysicalCubeWindow root D (residueProfileWidth q V),
      v + physicalResidueOffsetShift root root₀ D D₀ (boundedColumnResidueRepresentative q a.val) q ∈ window)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E Z : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (he : ∀ a : cells, ∀ v ∈ window,
      ‖((A * (((smoothProductPMF (residueProfileWidth q V)
        (residueProfileWidth_pos q V hq hV)).map (centeredPhysicalCubeMap root D))
          (v - physicalResidueOffsetShift root root₀ D D₀
            (boundedColumnResidueRepresentative q a.val) q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E) :
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let F := fun a : cells => physicalResidueReconstruction root₀ D₀ base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
          φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q a.val) q z)) /
          (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      (∑ a : cells, selectedResidueCellWeight q cells V a *
        ((E/A) * ∑ v ∈ window, ‖φ (F a v)‖)) / Z := by
  classical
  intro Q hQ F
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  apply div_le_div_of_nonneg_right _ hZ.le
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (selectedResidueCellWeight_nonneg q cells V a)]
  exact mul_le_mul_of_nonneg_left
    (smoothPhysicalResidue_reference_window_error root root₀ D D₀ base
      (boundedColumnResidueRepresentative q a.val) q hq modulus hres Q hQ window
      (hwindow a) ψ φ hA (he a)) (selectedResidueCellWeight_nonneg q cells V a)

end Erdos3.BooleanCubeKernel

end

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
theorem allocatedTrimmedSpatial_reference_window
    (u : PrincipalAxisTuples (α := α) grid sides)
    (w w₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    {X : Type*} [Fintype X] (N q : X → ℕ)
    (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (r : Option vars × X → ℤ) (hr : ∀ k d, |(r (k,d) : ℝ)| ≤ q d)
    (period modulus : ℕ) (hdiv : ∀ d, q d * period ∣ modulus)
    (hlabel : principalResidueLabel modulus w = principalResidueLabel modulus w₀)
    (hsmall : ∀ d, 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ trimmedSpatialRootScale τ N q d)
    (v : X → (Unit ⊕ α) → ℤ)
    (hv : v ∈ centeredPhysicalCubeWindow
      (allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w))
      (residueProfileWidth q (trimmedSpatialWidths (K := vars) W τ N))) :
    v + physicalResidueOffsetShift
      (allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w))
      (allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w₀))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w₀)) r q ∈
      spatialWindow (trimmedSpatialRootScale τ N q) 4 := by
  let H := trimmedSpatialRootScale τ N q
  let shift := physicalResidueOffsetShift
    (allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w))
    (allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w₀))
    (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w))
    (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w₀)) r q
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hbound := (allocatedPhysicalResidue_offset_shift B U basis S c x u w w₀
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
      (allocatedTrimmedSpatial_window_bound B U basis S c x (principalAxisJoin grid u w)
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
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

omit [DecidableEq G] [Fintype α] [DecidableEq α] in
include x in
theorem allocatedPrincipalColumns_difference_sum_bound (i : Unit ⊕ α) :
    (∑ j, |((cols i j - refcols i j : ℤ) : ℝ)|) ≤
      Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
        (2 * allocatedPhysicalEntryBudget B U basis S c) := by
  have hentry (z : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) (j) :
      |(principalSpatialColumns (fun j => c (Sum.inr j)) id z i j : ℝ)| ≤
        allocatedPhysicalEntryBudget B U basis S c := by
    rw [← allocatedPhysicalCube_principal_columns B U basis S c x z i j]
    exact allocatedPhysicalCube_coefficient_entry_bound B U basis S c x z i (some (Sum.inr j))
  calc
    _ ≤ ∑ _j : PrincipalTupleIndex B (layerSamplerDegree I n),
        2 * allocatedPhysicalEntryBudget B U basis S c := by
      apply Finset.sum_le_sum
      intro j _
      rw [Int.cast_sub]
      exact (abs_sub _ _).trans (by linarith [hentry y j, hentry y₀ j])
    _ = _ := by simp

theorem allocatedTrimmedSpatial_shifted_vector_site_error (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ δ b r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hprincipalRoot : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * (1 + W))
    (hprincipalDir : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * S.value)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ τ * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (residue : Option vars × X → ℤ) (hresidue : ∀ k d, |(residue (k,d) : ℝ)| ≤ q d)
    (hCR : ∀ d, integerResidueMatrix cols (q d * modulus) =
      integerResidueMatrix refcols (q d * modulus))
    (hδ : 0 ≤ δ)
    (hmove : ∀ d i, (∑ j, |((cols i j - refcols i j : ℤ) : ℝ)|) ≤
      δ * trimmedSpatialRootScale τ N q d)
    (hb : 0 < b) (hr : 0 < r) (v : X → (Unit ⊕ α) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / trimmedSpatialRootScale τ N q d| ≤ b) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := trimmedSpatialWidths (K := vars) W τ N
    let hV := trimmedSpatialWidths_pos (K := vars) hW hτ N hN
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let E := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    let shift := physicalResidueOffsetShift root (allocatedPhysicalCubeRoot B U basis S c x y₀)
      dirs (allocatedPhysicalCubeDirections B U basis S x y₀) residue q
    let E' := E + G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * δ
    ‖(((∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i) *
        (((smoothProductPMF Q hQ).map (fun z d => physicalCubeCoefficient root dirs *ᵥ
          (fun k => z (k, d)))) (v - shift)).toReal : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix refcols modulus))) modulus f (H d) b r (v d)‖ ≤
      Fintype.card X * (E' + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
        (1 + G₀ * anisotropicSpatialDensityCap selection κ + E') ^ Fintype.card X := by
  classical
  intro H T V hV Q hQ hpivot f E G₀ shift E'
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hT (d) : 0 < T d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2
  have hroot (g : G) : |(ker g : ℝ)| ≤ 1 + W := by
    have h : |(ker g : ℝ)| ≤ W :=
      (allocatedPhysicalCube_root_budget B U basis S c x y (.inl g)).trans hbudget
    linarith
  have hD (i : α) (g : G) : |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value :=
    allocatedPhysicalCube_directions_bound B U basis S x y i (.inl g)
  have hminor : κ ≤ |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) /
      (S.value : ℝ))).det| := by
    change κ ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hE : 0 ≤ E := anisotropicSpatialError_nonneg selection _ M hκ.le
    (zero_le_one.trans hC₀) hρ.le hξ0
  have hpoint (d) := allocatedTrimmedSpatial_kernel_error B U basis S c x y selection N q d hN hq
    hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ0 hξ1 hprincipalRoot hprincipalDir (hsize d) hmesh
  have hshift : shift = fun d => residueMatrixShift cols refcols (q d)
      (fun j => residue (some (Sum.inr j), d)) :=
    allocatedPhysicalResidue_shift_principal B U basis S c x y y₀ residue q
  rw [hshift, smoothProductPMF_matrix_image_scaled]
  exact canonicalVectorSpatialSiteApprox_shift_error selection ker (scalarCubeDifferenceMatrix x) hpivot
    (fun _ => cols) (fun _ => refcols) H T hH hT hW (Nat.cast_pos.mpr S.positive)
    (by exact_mod_cast S.positive) hκ (fun d => trimmedSpatial_scale_ratio hW N q d)
    hroot hD hminor modulus hperiod q hq (fun d j => residue (some (Sum.inr j), d))
    (fun d j => hresidue (some (Sum.inr j)) d) hCR hδ hmove _ hE hb hr hpoint v hv

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

theorem allocatedTrimmedSpatial_reference_site_test (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ δ r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hprincipalRoot : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * (1 + W))
    (hprincipalDir : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * S.value)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ τ * (N d : ℝ))
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
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (trimmedSpatialWidths W τ N) z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {Cφ Z : ℝ}
    (hCφ : 0 ≤ Cφ) (hφ : ∀ v, ‖φ v‖ ≤ Cφ) (hZ : 0 < Z) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := trimmedSpatialWidths (K := vars) W τ N
    let hV := trimmedSpatialWidths_pos (K := vars) hW hτ N hN
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
    let Cwin := 9 ^ Fintype.card (X × (Unit ⊕ α)) *
      (((1 + W) / (S.value : ℝ)) ^ Fintype.card α) ^ Fintype.card X
    let window := spatialWindow H 4
    let F := fun a : cells => physicalResidueReconstruction root₀ dirs₀ base
      (boundedColumnResidueRepresentative q a.val) q
    ‖(∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root dirs base z)) / (Z : ℂ) -
      (∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
        ∑ v ∈ window, (ψ v / (A : ℂ)) * φ (F a v)) / (Z : ℂ)‖ ≤
      Cφ * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option vars × X) / ρ + E * Cwin) / Z := by
  classical
  intro H T V hV Q hpivot f ψ A E₀ G₀ E₁ E Cwin window F
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hT (d) : 0 < T d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2
  have hshiftSmall (d) : 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ H d :=
    hρshift.trans (trimmedSpatial_scale_lower hW hρ.le N q d (hq d) (hsize d)).1
  have hmoveSmall (d) : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c) ≤ δ * H d :=
    hρmove.trans (mul_le_mul_of_nonneg_left
      (trimmedSpatial_scale_lower hW hρ.le N q d (hq d) (hsize d)).1 hδ)
  have hA : 0 < A := Finset.prod_pos (fun d _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos α (hH d) (hT d) (Nat.cast_pos.mpr S.positive) i))
  have hCR (d) : integerResidueMatrix cols (q d * modulus) =
      integerResidueMatrix refcols (q d * modulus) := by
    apply integerResidueMatrix_reduce _ _ (hdiv d)
    rw [principalSpatialColumns_join_residue, principalSpatialColumns_join_residue, hlabel]
  have hphysical (d) : integerResidueMatrix (physicalCubeCoefficient root dirs) (q d * modulus) =
      integerResidueMatrix (physicalCubeCoefficient root₀ dirs₀) (q d * modulus) :=
    integerResidueMatrix_reduce _ _ (hdiv d)
      (allocatedPhysicalCube_residue_of_principal_label B U basis S c x u w w₀ refined hlabel)
  have hrep (a : cells) (k) (d) :
      |(boundedColumnResidueRepresentative q a.val (k,d) : ℝ)| ≤ q d := by
    have h := boundedColumnResidueRepresentative_bounds q hq a.val (k,d)
    rw [abs_of_nonneg (by exact_mod_cast h.1 :
      (0 : ℝ) ≤ boundedColumnResidueRepresentative q a.val (k,d))]
    exact_mod_cast h.2.le
  have hwindow (a : cells) (v) (hv : v ∈ centeredPhysicalCubeWindow root dirs Q) :
      v + physicalResidueOffsetShift root root₀ dirs dirs₀
        (boundedColumnResidueRepresentative q a.val) q ∈ window :=
    allocatedTrimmedSpatial_reference_window B U basis S c x u w w₀ N q hN hq hW hτ hbudget
      (boundedColumnResidueRepresentative q a.val) (hrep a) modulus refined hdiv hlabel hshiftSmall v hv
  have he (a : cells) (v) (hv : v ∈ window) :
      ‖((A * (((smoothProductPMF Q (residueProfileWidth_pos q V hq hV)).map
        (centeredPhysicalCubeMap root dirs))
          (v - physicalResidueOffsetShift root root₀ dirs dirs₀
            (boundedColumnResidueRepresentative q a.val) q)).toReal : ℝ) : ℂ) - ψ v‖ ≤ E :=
    allocatedTrimmedSpatial_shifted_vector_site_error B U basis S c x y y₀ selection N q hN hq
      hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ0 hξ1 hprincipalRoot hprincipalDir hsize hmesh
      modulus hperiod (boundedColumnResidueRepresentative q a.val) (hrep a) hCR hδ
      (fun d i => (allocatedPrincipalColumns_difference_sum_bound B U basis S c x y y₀ i).trans (hmoveSmall d))
      (by norm_num : (0 : ℝ) < 4) hr v ((mem_spatialWindow_scaled_iff H hH 4 v).mp hv)
  have hρ1 : 1 ≤ ρ := by linarith [probabilityProfileLipschitz_one_le]
  have hcard : (window.card : ℝ) ≤ Cwin * A := by
    have h := spatialWindow_card_anisotropic (α := α) H T
      (fun d => hρ1.trans (trimmedSpatial_scale_lower hW hρ.le N q d (hq d) (hsize d)).1)
      (by norm_num : (0 : ℝ) ≤ 4)
      (Nat.cast_ne_zero.mpr S.positive.ne') (fun d => trimmedSpatial_scale_ratio hW N q d)
    simpa only [show 2 * (4 : ℝ) + 1 = 9 by norm_num] using h
  have hE₀ : 0 ≤ E₀ := anisotropicSpatialError_nonneg selection _ M hκ.le
    (zero_le_one.trans hC₀) hρ.le hξ0
  have hcap := anisotropicSpatialDensityCap_nonneg selection hκ.le
  have hlip := anisotropicSpatialDensityLip_nonneg selection hκ.le
  have hE : 0 ≤ E := by dsimp only [E, E₁, G₀]; positivity
  have hmassBound := selectedResidue_site_mass_bound q cells V hV hmass window
    (fun a v => φ (F a v)) hA hE hCφ (fun _ _ _ => hφ _) hcard
  have hrec := physicalSelectedResidue_trimmed_recenter root dirs base q N hq hN cells
    hW hτ hρ8 hsize hmass φ hCφ hφ hZ
  have hsite := physicalCenteredResidueMixture_reference_error root root₀ dirs dirs₀ base q hq modulus hphysical
    cells V hV window hwindow ψ φ hA hZ he
  have h := (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    (add_le_add hrec (hsite.trans (div_le_div_of_nonneg_right hmassBound hZ.le)))
  exact h.trans_eq (by ring)

end Erdos3.VectorPolynomial

end

end OAI
