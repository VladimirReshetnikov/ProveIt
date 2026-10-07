import OAI.Combinatorics.Progressions.Linear.AllocatedKernelSiteMask
import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridChartModelMeasurable

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y₀
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

noncomputable def allocatedClippedPrefactorSiteMask
    (r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ :=
  allocatedKernelSiteMask B U b S rowSets x q residue period (fun s => (r s).1) *
    coefficientDeckSiteMask root dirs rows d period (fun s => (r s).2)

theorem allocatedClippedPrefactorSiteMask_reconstructed
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (z : MixedCoveredJetSource I rowTypes E n d) :
    allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
      (fun s => (fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period),
        fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ZMod period))) =
      coefficientDeckJetDensity root dirs rows d z.2 *
        ∏ a, allocatedLongJetMask B U b S x rows q residue a ((split z.1).2 a) := by
  rw [allocatedClippedPrefactorSiteMask,
    allocatedKernelSiteMask_reconstructed B U b S rowSets x q residue period hperiod d z,
    coefficientDeckRowsSiteMask_reconstructed root dirs rowSets d period
      (fun j => (hperiod j).trans (allocatedWholeJetMatrix_kernel_range_le B U b S x y₀ rows j)) z]
  exact mul_comm _ _

theorem allocatedClippedPrefactorSiteMask_bound
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue j) z ≤ C)
    (r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) :
    |allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period r| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period := by
  have hd := coefficientDeckSiteMask_bounds root dirs rows d period
    (fun j => (hperiod j).trans (allocatedWholeJetMatrix_kernel_range_le B U b S x y₀ rows j))
    (fun s => (r s).2)
  rw [allocatedClippedPrefactorSiteMask, abs_mul, abs_of_nonneg hd.1]
  exact mul_le_mul (allocatedKernelSiteMask_bound B U b S rowSets x q residue period hC hm _)
    hd.2 hd.1 (pow_nonneg (zero_le_one.trans hC) _)

theorem allocatedClippedPrefactorSiteMask_expansion
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {K : Type*} [Fintype K] (c : K → ℂ)
    (f : K → Finset α → MixedCoveredJetSource I (fun _ => Unit) E n d → ℂ)
    (z : MixedCoveredJetSource I rowTypes E n d) :
    ((coefficientDeckJetDensity root dirs rows d z.2 *
        ∏ a, allocatedLongJetMask B U b S x rows q residue a ((split z.1).2 a) : ℝ) : ℂ) *
      (∑ k, c k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s)) =
    ∑ r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period), ∑ k,
      ((allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period r : ℂ) * c k) *
        ∏ s, maskedSiteFactor
          (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
            fun j i => ((v.2 j () i).val : ZMod period))) r f k s
          (mixedCoveredRowsSiteValue rowSets d z s) := by
  rw [maskedSiteExpansion_identity,
    allocatedClippedPrefactorSiteMask_reconstructed B U b S rowSets x y₀ q d period hperiod z]

theorem allocatedClippedPrefactorSiteMask_coefficient_sum
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {C A : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j q (residue j) z ≤ C)
    {K : Type*} [Fintype K] (c : K → ℂ) (hc : (∑ k, ‖c k‖) ≤ A) :
    (∑ r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period), ∑ k,
      ‖(allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period r : ℂ) * c k‖) ≤
      (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
        Fintype.card (Finset α) *
      (C ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * A := by
  apply maskedSiteExpansion_coefficient_sum _ c
    (mul_nonneg (pow_nonneg (zero_le_one.trans hC) _) (coefficientDeckPeriodCap_nonneg rowTypes E period)) _ hc
  intro r
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact allocatedClippedPrefactorSiteMask_bound B U b S rowSets x y₀ q d period hperiod hC hm r

variable (T : Fin m → ℝ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

omit [Fintype α] in
theorem allocatedClippedFullGridGlobalPrefactor_components
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedClippedFullGridGlobalPrefactor B U b S rowSets d T x hb o bW q y₀ f (chart z) =
      (if allocatedPhysicalGridCondition B U b S rowTypes T ((split z.1).1) then 1 else 0) *
        ((coefficientDeckJetDensity root dirs rows d z.2 *
          (∏ a, allocatedLongJetMask B U b S x rows q residue a ((split z.1).2 a)) *
          f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
          (allocatedFullGridNaturalVolume B U b S rowSets * coveredJetArrayScale (O := rowTypes) U *
            ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a) : ℝ) : ℂ) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d
    (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  rw [allocatedClippedFullGridGlobalPrefactor,
    allocatedPhysicalGridMask_apply B U b S rowTypes T hb o bW d z hz]
  unfold allocatedWholeMaskedGridlessProfile allocatedGridlessCoveredProfile
  rw [restrictedChartDensity_apply _ _ _ _ hinj hz]
  simp only [one_mul, principalAxisJoin_restrict, allocatedLongProfileDensity,
    Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv, mul_inv_rev]
  ring

theorem allocatedClippedFullGridGlobalPrefactor_site_masks
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedClippedFullGridGlobalPrefactor B U b S rowSets d T x hb o bW q y₀ f (chart z) =
      (if allocatedPhysicalGridCondition B U b S rowTypes T ((split z.1).1) then 1 else 0) *
        ((allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
          (fun s => (fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period),
            fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ZMod period))) *
          f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
          (allocatedFullGridNaturalVolume B U b S rowSets * coveredJetArrayScale (O := rowTypes) U *
            ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a) : ℝ) : ℂ) := by
  rw [allocatedClippedPrefactorSiteMask_reconstructed B U b S rowSets x y₀ q d period hperiod z]
  exact allocatedClippedFullGridGlobalPrefactor_components B U b S rowSets x y₀ q d T hb o bW f z hz

theorem allocatedClippedFullGridGlobalPrefactor_site_expansion
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {K : Type*} [Fintype K] (c : K → ℂ)
    (g : K → Finset α → MixedCoveredJetSource I (fun _ => Unit) E n d → ℂ)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedClippedFullGridGlobalPrefactor B U b S rowSets d T x hb o bW q y₀ f (chart z) *
      (∑ k, c k * ∏ s, g k s (mixedCoveredRowsSiteValue rowSets d z s)) =
    (if allocatedPhysicalGridCondition B U b S rowTypes T ((split z.1).1) then 1 else 0) *
      ((f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
        (allocatedFullGridNaturalVolume B U b S rowSets * coveredJetArrayScale (O := rowTypes) U *
          ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a) : ℝ) : ℂ) *
      ∑ r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period), ∑ k,
        ((allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period r : ℂ) * c k) *
          ∏ s, maskedSiteFactor
            (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
              fun j i => ((v.2 j () i).val : ZMod period))) r g k s
            (mixedCoveredRowsSiteValue rowSets d z s) := by
  rw [allocatedClippedFullGridGlobalPrefactor_site_masks B U b S rowSets x y₀ q d period
    T hb o bW f hperiod z hz, maskedSiteExpansion_identity]
  simp only [Complex.ofReal_mul, div_eq_mul_inv]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y₀
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedProductFullGridPrefactor_components
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) =
      allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) *
        ((coefficientDeckJetDensity root dirs rows d z.2 *
          (∏ a, allocatedLongJetMask B U b S x rows q residue a ((split z.1).2 a)) *
          f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
          (allocatedFullGridNaturalVolume B U b S rowSets * coveredJetArrayScale (O := rowTypes) U *
            ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a) : ℝ) : ℂ) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d
    (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  rw [allocatedProductFullGridPrefactor]
  unfold allocatedWholeMaskedGridlessProfile allocatedGridlessCoveredProfile
  rw [restrictedChartDensity_apply _ _ _ _ hinj hz]
  simp only [one_mul, principalAxisJoin_restrict, allocatedLongProfileDensity,
    Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv, mul_inv_rev]
  ring

theorem allocatedProductFullGridPrefactor_site_masks
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) =
      allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) *
        ((allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
          (fun s => (fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period),
            fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ZMod period))) *
          f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
          (allocatedFullGridNaturalVolume B U b S rowSets * coveredJetArrayScale (O := rowTypes) U *
            ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a) : ℝ) : ℂ) := by
  rw [allocatedClippedPrefactorSiteMask_reconstructed B U b S rowSets x y₀ q d period hperiod z]
  exact allocatedProductFullGridPrefactor_components B U b S rowSets x y₀ q d r hr hb o bW f z hz

theorem allocatedProductFullGridPrefactor_site_expansion
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    {K : Type*} [Fintype K] (c : K → ℂ)
    (g : K → Finset α → MixedCoveredJetSource I (fun _ => Unit) E n d → ℂ)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) *
      (∑ k, c k * ∏ s, g k s (mixedCoveredRowsSiteValue rowSets d z s)) =
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) *
      ((f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
        (allocatedFullGridNaturalVolume B U b S rowSets * coveredJetArrayScale (O := rowTypes) U *
          ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a) : ℝ) : ℂ) *
      ∑ r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period), ∑ k,
        ((allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period r : ℂ) * c k) *
          ∏ s, maskedSiteFactor
            (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
              fun j i => ((v.2 j () i).val : ZMod period))) r g k s
            (mixedCoveredRowsSiteValue rowSets d z s) := by
  rw [allocatedProductFullGridPrefactor_site_masks B U b S rowSets x y₀ q d period
    r hr hb o bW f hperiod z hz, maskedSiteExpansion_identity]
  simp only [Complex.ofReal_mul, div_eq_mul_inv]
  ring

end Erdos3.VectorPolynomial

end

end OAI
