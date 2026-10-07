import OAI.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio
import OAI.Combinatorics.Progressions.Lattices.SelectedResidueRefinementMean

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def physicalCubeResidueCoordinates {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (z : Option K × X → ℤ) :
    X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeRootDifferences root D base residue x i +
    (modulus x : ℤ) * physicalCubeRootDifferences root D 0 z x i

theorem physicalCubeRootDifferences_residue {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (z : Option K × X → ℤ) :
    physicalCubeRootDifferences root D base (residueLatticeArray residue modulus z) =
      physicalCubeResidueCoordinates root D base residue modulus z := by
  funext x i
  have hoff : physicalCubeOffset (0 : X → ℤ) x i = 0 := by cases i <;> rfl
  simp only [physicalCubeResidueCoordinates, physicalCubeRootDifferences,
    residueLatticeArray, hoff, zero_add, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

noncomputable def physicalCubeResidueLaw {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) : PMF (X → (Unit ⊕ α) → ℤ) :=
  (residueSmoothIndexPMF residue modulus hmodulus V hV hZ).map
    (physicalCubeResidueCoordinates root D base residue modulus)

theorem physicalCubeResidueLaw_eq_map {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) :
    (residueSmoothPMF residue modulus hmodulus V hV hZ).map
        (physicalCubeRootDifferences root D base) =
      physicalCubeResidueLaw root D base residue modulus hmodulus V hV hZ := by
  rw [residueSmoothPMF, PMF.map_comp]
  congr 1
  funext z
  exact physicalCubeRootDifferences_residue root D base residue modulus z

theorem physicalCubeResidueLaw_expectation {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) :
    (∑' z, ((residueSmoothPMF residue modulus hmodulus V hV hZ z).toReal : ℂ) *
      φ (physicalCubeRootDifferences root D base z)) =
      ∑' z, ((residueSmoothIndexPMF residue modulus hmodulus V hV hZ z).toReal : ℂ) *
        φ (physicalCubeResidueCoordinates root D base residue modulus z) := by
  rw [residueSmoothPMF_expectation]
  simp_rw [physicalCubeRootDifferences_residue]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators Matrix

def physicalCubeIndexCoordinates {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (z : Option K × X → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun x => physicalCubeCoefficient root D *ᵥ (fun k => z (k, x))

def physicalResidueReconstruct {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ)
    (v : X → (Unit ⊕ α) → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeRootDifferences root D base residue x i + (modulus x : ℤ) * v x i

theorem physicalCubeResidueCoordinates_index {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (z : Option K × X → ℤ) :
    physicalCubeResidueCoordinates root D base residue modulus z =
      physicalResidueReconstruct root D base residue modulus (physicalCubeIndexCoordinates root D z) := by
  funext x i
  have hzero : physicalCubeOffset (0 : X → ℤ) x i = 0 := by cases i <;> rfl
  simp only [physicalCubeResidueCoordinates, physicalResidueReconstruct,
    physicalCubeIndexCoordinates, physicalCubeRootDifferences, hzero, zero_add,
    Matrix.mulVec, dotProduct]

theorem physicalResidue_index_test_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V))
    (proxy : (X → (Unit ⊕ α) → ℤ) → ℝ) (hg : Integrable proxy Measure.count)
    {ε B : ℝ} (hB : 0 ≤ B)
    (he : (∫ v, |(((residueSmoothIndexPMF residue modulus hmodulus V hV hZ).map
      (physicalCubeIndexCoordinates root D)) v).toReal - proxy v| ∂Measure.count) ≤ ε)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) (hφ : ∀ v, ‖φ v‖ ≤ B) :
    ‖(∑' z, ((residueSmoothPMF residue modulus hmodulus V hV hZ z).toReal : ℂ) *
      φ (physicalCubeRootDifferences root D base z)) -
      ∫ v, (proxy v : ℂ) * φ (physicalResidueReconstruct root D base residue modulus v)
        ∂Measure.count‖ ≤ B * ε := by
  rw [physicalCubeResidueLaw_expectation]
  simp_rw [physicalCubeResidueCoordinates_index]
  exact pmf_image_count_test_error (residueSmoothIndexPMF residue modulus hmodulus V hV hZ)
    (physicalCubeIndexCoordinates root D) proxy hg hB he
    (fun v => φ (physicalResidueReconstruct root D base residue modulus v)) (fun v => hφ _)

theorem selectedResidue_physical_index_test_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (T : Finset (ColumnResiduePattern (Option K) X modulus))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (hc : ∀ r : T, 0 < shiftedSmoothProductMass
      (residueProfileCenter (boundedColumnResidueRepresentative modulus r.val) modulus)
      (residueProfileWidth modulus V))
    (proxy : T → (X → (Unit ⊕ α) → ℤ) → ℝ) (hg : ∀ r, Integrable (proxy r) Measure.count)
    (ε : T → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (he : ∀ r : T, (∫ v, |(((residueSmoothIndexPMF
      (boundedColumnResidueRepresentative modulus r.val) modulus hmodulus V hV (hc r)).map
      (physicalCubeIndexCoordinates root D)) v).toReal - proxy r v| ∂Measure.count) ≤ ε r)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) (hφ : ∀ v, ‖φ v‖ ≤ B) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
      φ (physicalCubeRootDifferences root D base z)) -
      ∑ r : T, (selectedResidueCellWeight modulus T V r : ℂ) *
        ∫ v, (proxy r v : ℂ) * φ (physicalResidueReconstruct root D base
          (boundedColumnResidueRepresentative modulus r.val) modulus v) ∂Measure.count‖ ≤
      B * ∑ r : T, selectedResidueCellWeight modulus T V r * ε r := by
  have h := selectedResidue_bounded_mixture_error modulus hmodulus T V hV hZ hc
    (fun z => φ (physicalCubeRootDifferences root D base z))
    (fun r => ∫ v, (proxy r v : ℂ) * φ (physicalResidueReconstruct root D base
      (boundedColumnResidueRepresentative modulus r.val) modulus v) ∂Measure.count)
    (fun r => B * ε r) (fun r => physicalResidue_index_test_error root D base _ modulus hmodulus
      V hV (hc r) (proxy r) (hg r) hB (he r) φ hφ)
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def physicalResidueCoordinateMap {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (x : X)
    (z : Option K → ℤ) (i : Unit ⊕ α) : ℤ :=
  physicalCubeRootDifferences root D base residue x i +
    (modulus x : ℤ) * (physicalCubeCoefficient root D *ᵥ z) i

theorem physicalCubeResidueCoordinates_grouped {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) :
    physicalCubeResidueCoordinates root D base residue modulus =
      (fun z x => physicalResidueCoordinateMap root D base residue modulus x (z x)) ∘
        spatialCoordinateArrayEquiv (Option K) X := by
  funext z x i
  unfold physicalCubeResidueCoordinates physicalResidueCoordinateMap
  congr 1
  have hzero : physicalCubeOffset (0 : X → ℤ) x i = 0 := by cases i <;> rfl
  simp only [physicalCubeRootDifferences, hzero, zero_add, Matrix.mulVec, dotProduct,
    spatialCoordinateArrayEquiv, Equiv.coe_fn_mk]

noncomputable def physicalResidueCoordinateLaw {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) (x : X) : PMF ((Unit ⊕ α) → ℤ) :=
  (shiftedSmoothProductPMF
    (fun k => residueProfileCenter residue modulus (k, x))
    (fun k => residueProfileWidth modulus V (k, x))
    (fun k => residueProfileWidth_pos modulus V hmodulus hV (k, x))
    (shiftedSmoothProductMass_slice_pos _ _ (residueProfileWidth_pos modulus V hmodulus hV) hZ x)).map
      (physicalResidueCoordinateMap root D base residue modulus x)

theorem physicalCubeResidueLaw_product {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus)
      (residueProfileWidth modulus V)) :
    physicalCubeResidueLaw root D base residue modulus hmodulus V hV hZ =
      dependentProductPMF (physicalResidueCoordinateLaw root D base residue modulus hmodulus V hV hZ) := by
  unfold physicalCubeResidueLaw residueSmoothIndexPMF
  rw [physicalCubeResidueCoordinates_grouped, ← PMF.map_comp,
    shiftedSmoothProductPMF_grouped,
    dependentProductPMF_map]
  rfl

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSelectedResidue_recenter_test {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    (hlarge : ∀ z, 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {B Z : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) (hZ : 0 < Z) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * ∑ z : Option K × X, (q z.2 : ℝ) / V z)) / Z := by
  have h := selectedResidueSmoothPMF_recenter_test q hq T V hV hmass hlarge
    (fun z => φ (physicalCubeRootDifferences root D base z)) hB (fun z => hφ _)
  simp_rw [physicalCubeRootDifferences_residue] at h
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  exact div_le_div_of_nonneg_right h hZ.le

theorem trimmedSpatial_residue_width_lower {K X : Type*} {W τ ρ : ℝ}
    (hW : 0 ≤ W) (hρ : 0 ≤ ρ) (N q : X → ℕ) (hq : ∀ x, 0 < q x)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * ρ ≤ τ * (N x : ℝ))
    (z : Option K × X) :
    ρ ≤ residueProfileWidth q (trimmedSpatialWidths W τ N) z := by
  have h := trimmedSpatial_scale_lower hW hρ N q z.2 (hq z.2) (hsize z.2)
  have he := congrFun (trimmedSpatial_residue_scale (K := K) W τ N q z.2) z.1
  rw [he]
  cases z.1
  · exact h.1
  · exact h.2

theorem physicalSelectedResidue_trimmed_recenter {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q N : X → ℕ) (hq : ∀ x, 0 < q x) (hN : ∀ x, 0 < N x)
    (T : Finset (ColumnResiduePattern (Option K) X q))
    {W τ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (hρ : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * ρ ≤ τ * (N x : ℝ))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T (trimmedSpatialWidths W τ N) z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {B Z : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) (hZ : 0 < Z) :
    let V := trimmedSpatialWidths (K := K) W τ N
    let hV := trimmedSpatialWidths_pos (K := K) hW hτ N hN
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option K × X) / ρ)) / Z := by
  intro V hV
  have hρ0 : 0 < ρ := by linarith [probabilityProfileLipschitz_one_le]
  have hw (z : Option K × X) : ρ ≤ residueProfileWidth q V z :=
    trimmedSpatial_residue_width_lower hW hρ0.le N q hq hsize z
  have hratio (z : Option K × X) : (q z.2 : ℝ) / V z ≤ 1 / ρ := by
    have hq0 : (0 : ℝ) < q z.2 := by exact_mod_cast hq z.2
    have h := (le_div_iff₀ hq0).mp (hw z)
    apply (div_le_div_iff₀ (hV z) hρ0).mpr
    linarith
  have hsum : (∑ z : Option K × X, (q z.2 : ℝ) / V z) ≤ Fintype.card (Option K × X) / ρ := by
    apply (Finset.sum_le_sum (fun z _ => hratio z)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  apply (physicalSelectedResidue_recenter_test root D base q hq T V hV hmass
    (fun z => hρ.trans (hw z)) φ hB hφ hZ).trans
  apply div_le_div_of_nonneg_right _ hZ.le
  apply mul_le_mul_of_nonneg_left _ hB
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 24 * (probabilityProfileLipschitz : ℝ) by positivity)

noncomputable def physicalRecenteringScale (K X : Type*) [Fintype K] [Fintype X]
    (B ε : ℝ) : ℝ :=
  8 * (probabilityProfileLipschitz : ℝ) +
    2 * (B * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option K × X))) / ε

theorem physicalSelectedResidue_prescribed_recenter {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q N : X → ℕ) (hq : ∀ x, 0 < q x) (hN : ∀ x, 0 < N x)
    (T : Finset (ColumnResiduePattern (Option K) X q)) (hT : T.Nonempty)
    {W τ B ε : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * physicalRecenteringScale K X B ε ≤ τ * (N x : ℝ)) :
    let V := trimmedSpatialWidths (K := K) W τ N
    let hV := trimmedSpatialWidths_pos (K := K) hW hτ N hN
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z,
    ∀ (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) (_hφ : ∀ v, ‖φ v‖ ≤ B)
      {Z : ℝ} (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ 2),
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ)‖ ≤ ε := by
  intro V hV
  let C := B * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option K × X))
  let ρ := physicalRecenteringScale K X B ε
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ := by
    dsimp only [ρ, physicalRecenteringScale]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hC) hε.le)
  have hρ0 : 0 < ρ := by linarith [probabilityProfileLipschitz_one_le]
  have hw (z : Option K × X) : 8 * (probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth q V z :=
    hρ8.trans (trimmedSpatial_residue_width_lower hW hρ0.le N q hq hsize z)
  have hc (r : T) : 0 < ∑' z, residueSmoothWeight (columnResidueRepresentative q r.val) q V z := by
    rw [← residueSmoothWeight_mass _ q hq V hV]
    exact shiftedSmoothProductMass_pos_of_large _ _ hw
  have hmass := selectedResidueSmoothWeight_mass_pos q T hT V hV hc
  refine ⟨hmass, ?_⟩
  intro φ hφ Z hZ hZi
  apply (physicalSelectedResidue_trimmed_recenter root D base q N hq hN T hW hτ hρ8 hsize
    hmass φ hB hφ hZ).trans
  have hpart : 2 * C / ε ≤ ρ := by
    dsimp only [ρ, physicalRecenteringScale, C]
    exact le_add_of_nonneg_left (by positivity)
  have hbudget : 2 * C / ρ ≤ ε := by
    apply (div_le_iff₀ hρ0).mpr
    simpa only [mul_comm ρ ε] using (div_le_iff₀ hε).mp hpart
  calc
    _ = (C / ρ) * Z⁻¹ := by dsimp only [C]; ring
    _ ≤ (C / ρ) * 2 := mul_le_mul_of_nonneg_left hZi (div_nonneg hC hρ0.le)
    _ = 2 * C / ρ := by ring
    _ ≤ ε := hbudget

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def physicalResidueReconstruction {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (v : X → (Unit ⊕ α) → ℤ) :
    X → (Unit ⊕ α) → ℤ :=
  fun d i => physicalCubeRootDifferences root D base residue d i + (q d : ℤ) * v d i

theorem physicalResidueReconstruction_centered {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ) (z : Option K × X → ℤ) :
    physicalResidueReconstruction root D base residue q (centeredPhysicalCubeMap root D z) =
      physicalCubeResidueCoordinates root D base residue q z := by
  rw [centeredPhysicalCubeMap_eq]
  rfl

theorem smoothPhysicalResidue_finite_expectation {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ)
    (Q : Option K × X → ℝ) (hQ : ∀ z, 0 < Q z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) :
    (∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
      φ (physicalCubeResidueCoordinates root D base residue q z)) =
    ∑ v ∈ centeredPhysicalCubeWindow root D Q,
      (((smoothProductPMF Q hQ).map (centeredPhysicalCubeMap root D) v).toReal : ℂ) *
        φ (physicalResidueReconstruction root D base residue q v) := by
  classical
  have h := pmf_image_finite_expectation (smoothProductPMF Q hQ)
    (rectangularWeightIndices 0 Q 1) (smoothProductPMF_toReal_zero_off Q hQ)
    (centeredPhysicalCubeMap root D) (centeredPhysicalCubeWindow root D Q)
    (centeredPhysicalCubeMap_mem_window root D Q)
    (fun v => φ (physicalResidueReconstruction root D base residue q v))
  simpa only [physicalResidueReconstruction_centered] using h

theorem smoothPhysicalResidue_site_error {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (residue : Option K × X → ℤ) (q : X → ℕ)
    (Q : Option K × X → ℝ) (hQ : ∀ z, 0 < Q z)
    (ψ φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {A E : ℝ} (hA : 0 < A)
    (he : ∀ v ∈ centeredPhysicalCubeWindow root D Q,
      ‖((A * (((smoothProductPMF Q hQ).map (centeredPhysicalCubeMap root D)) v).toReal : ℝ) : ℂ) -
        ψ v‖ ≤ E) :
    ‖(∑' z, ((smoothProductPMF Q hQ z).toReal : ℂ) *
        φ (physicalCubeResidueCoordinates root D base residue q z)) -
      ∑ v ∈ centeredPhysicalCubeWindow root D Q,
        (ψ v / (A : ℂ)) * φ (physicalResidueReconstruction root D base residue q v)‖ ≤
      (E / A) * ∑ v ∈ centeredPhysicalCubeWindow root D Q,
        ‖φ (physicalResidueReconstruction root D base residue q v)‖ := by
  classical
  have h := pmf_image_finite_test_error (smoothProductPMF Q hQ)
    (rectangularWeightIndices 0 Q 1) (smoothProductPMF_toReal_zero_off Q hQ)
    (centeredPhysicalCubeMap root D) (centeredPhysicalCubeWindow root D Q)
    (centeredPhysicalCubeMap_mem_window root D Q) ψ
    (fun v => φ (physicalResidueReconstruction root D base residue q v)) hA he
  simpa only [physicalResidueReconstruction_centered] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSelectedResidue_width_recenter {K X α : Type*} [Fintype K] [Fintype X]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (T : Finset (ColumnResiduePattern (Option K) X q))
    (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q T V z)
    {ρ : ℝ} (hρ : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hwidth : ∀ z, ρ ≤ residueProfileWidth q V z)
    (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) {B Z : ℝ}
    (hB : 0 ≤ B) (hφ : ∀ v, ‖φ v‖ ≤ B) (hZ : 0 < Z) :
    ‖(∑' z, ((selectedResidueSmoothPMF q T V hV hmass z).toReal : ℂ) *
        φ (physicalCubeRootDifferences root D base z)) / (Z : ℂ) -
      (∑ r : T, (selectedResidueCellWeight q T V r : ℂ) *
        ∑' z, ((smoothProductPMF (residueProfileWidth q V)
          (residueProfileWidth_pos q V hq hV) z).toReal : ℂ) *
            φ (physicalCubeResidueCoordinates root D base (boundedColumnResidueRepresentative q r.val) q z)) /
          (Z : ℂ)‖ ≤
      (B * (24 * (probabilityProfileLipschitz : ℝ) * Fintype.card (Option K × X) / ρ)) / Z := by
  have hρ0 : 0 < ρ := by linarith [probabilityProfileLipschitz_one_le]
  have hratio (z : Option K × X) : (q z.2 : ℝ) / V z ≤ 1 / ρ := by
    have hq0 : (0 : ℝ) < q z.2 := by exact_mod_cast hq z.2
    have h := (le_div_iff₀ hq0).mp (hwidth z)
    apply (div_le_div_iff₀ (hV z) hρ0).mpr
    linarith
  have hsum : (∑ z : Option K × X, (q z.2 : ℝ) / V z) ≤ Fintype.card (Option K × X) / ρ := by
    apply (Finset.sum_le_sum (fun z _ => hratio z)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  apply (physicalSelectedResidue_recenter_test root D base q hq T V hV hmass
    (fun z => hρ.trans (hwidth z)) φ hB hφ hZ).trans
  apply div_le_div_of_nonneg_right _ hZ.le
  apply mul_le_mul_of_nonneg_left _ hB
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 24 * (probabilityProfileLipschitz : ℝ) by positivity)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Matrix

def physicalResidueOffsetShift {K X α : Type*} [Fintype K]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) : X → (Unit ⊕ α) → ℤ :=
  fun d => residueMatrixShift (physicalCubeCoefficient root D) (physicalCubeCoefficient root₀ D₀)
    (q d) (fun k => r (k, d))

theorem physicalResidueOffsetShift_mem {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m)) (d : X) :
    physicalResidueOffsetShift root root₀ D D₀ r q d ∈ integerScalarLattice (Unit ⊕ α) (m : ℤ) :=
  (residueMatrixShift_spec _ _ (q d) m (hq d) (hres d) (fun k => r (k, d))).2

theorem physicalResidueReconstruction_offset_shift {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m))
    (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueReconstruction root D base r q v =
      physicalResidueReconstruction root₀ D₀ base r q
        (v + physicalResidueOffsetShift root root₀ D D₀ r q) := by
  funext d i
  have hs := (residueMatrixShift_spec _ _ (q d) m (hq d) (hres d) (fun k => r (k, d))).1 i
  change (q d : ℤ) * physicalResidueOffsetShift root root₀ D D₀ r q d i = _ at hs
  change physicalCubeOffset base d i +
      (physicalCubeCoefficient root D *ᵥ (fun k => r (k, d))) i + (q d : ℤ) * v d i =
    physicalCubeOffset base d i +
      (physicalCubeCoefficient root₀ D₀ *ᵥ (fun k => r (k, d))) i +
        (q d : ℤ) * (v d i + physicalResidueOffsetShift root root₀ D D₀ r q d i)
  rw [mul_add, hs, Matrix.sub_mulVec, Pi.sub_apply]
  ring

theorem physicalResidueOffsetShift_bound {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m))
    (hr : ∀ k d, |(r (k, d) : ℝ)| ≤ q d) (d : X) (i : Unit ⊕ α) :
    |(physicalResidueOffsetShift root root₀ D D₀ r q d i : ℝ)| ≤
      ∑ k, |((physicalCubeCoefficient root D i k - physicalCubeCoefficient root₀ D₀ i k : ℤ) : ℝ)| :=
  residueMatrixShift_bound _ _ (q d) m (hq d) (hres d) (fun k => r (k, d)) (fun k => hr k d) i

theorem physicalResidue_test_reference_offset {K X α : Type*} [Fintype K] [Fintype α]
    (root root₀ : K → ℤ) (D D₀ : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ d, 0 < q d) (m : ℕ)
    (hres : ∀ d, integerResidueMatrix (physicalCubeCoefficient root D) (q d * m) =
      integerResidueMatrix (physicalCubeCoefficient root₀ D₀) (q d * m))
    (mass : (X → (Unit ⊕ α) → ℤ) → ℝ) (φ : (X → (Unit ⊕ α) → ℤ) → ℂ) :
    (∑' v, (mass v : ℂ) * φ (physicalResidueReconstruction root D base r q v)) =
      ∑' v, (mass (v - physicalResidueOffsetShift root root₀ D D₀ r q) : ℂ) *
        φ (physicalResidueReconstruction root₀ D₀ base r q v) := by
  simp_rw [physicalResidueReconstruction_offset_shift root root₀ D D₀ base r q hq m hres]
  have h := (Equiv.addRight (physicalResidueOffsetShift root root₀ D D₀ r q)).tsum_eq
    (fun v => (mass (v - physicalResidueOffsetShift root root₀ D D₀ r q) : ℂ) *
      φ (physicalResidueReconstruction root₀ D₀ base r q v))
  simpa using h

end Erdos3.BooleanCubeKernel

end

end OAI
