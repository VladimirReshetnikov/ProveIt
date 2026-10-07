import OAI.Combinatorics.Progressions.Estimates.AllocatedRecenteredIdealError

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)
local notation "siteChart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "siteRegion" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "factor" => allocatedBufferedSiteChartFactor B U b S o hb bW d r hr

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

include hR hC hchart hbudget in
theorem allocatedBufferedRowDensityProduct_error {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (D : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ) (ε : ℝ) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (herr : ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ) -
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s)‖ ≤ ε) :
    ‖cutoff (chart z) * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
      ∑ k, a k * ∏ s, factor (f k s) (coveredRowsSiteValue rowSets U (chart z) s)‖ ≤ ε := by
  have hsum : (∑ k, a k * ∏ s, factor (f k s) (coveredRowsSiteValue rowSets U (chart z) s)) =
      cutoff (chart z) *
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s) := by
    simp_rw [allocatedBufferedRowIdealProduct B U b S o hb bW d r hr rowSets hR C hC hchart hbudget _ z hz]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, ← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_right (allocatedProductSiteCutoff_norm B U b S rowSets o hb bW d r hr _)
    (norm_nonneg _)).trans (by simpa only [one_mul] using herr)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

include hperiod hM hm in
theorem allocatedProductPrefactor_masked_density_error (hR : ∀ j, 0 < R j)
    {K : Type*} [Fintype K] (a : K → ℂ)
    (f : K → Finset α → MixedCoveredJetSource I (fun _ => Unit) E n d → ℂ)
    (D : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ) (ε : ℝ) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (herr : ‖cutoff (chart z) * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
      ∑ k, a k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s)‖ ≤ ε) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (D) (chart z) -
      ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
          ∏ s, maskedSiteFactor
            (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
              fun j i => ((v.2 j () i).val : ZMod period))) label f k s
              (mixedCoveredRowsSiteValue rowSets d z s)‖ ≤
      ‖inverseNormalizer‖ *
        (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * ε := by
  let label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) := fun s =>
    (fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period),
      fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ZMod period))
  have hmask : ‖(mask label : ℂ)‖ ≤
      M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact allocatedClippedPrefactorSiteMask_bound B U b S rowSets x y₀ q d period hperiod hM hm label
  have hcap : 0 ≤ M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period)
  have hV : ((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) ≠ 0 := by
    have hp : 0 < (∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) := Finset.prod_pos (fun i _ => hR i.1.val.1)
    exact_mod_cast hp.ne'
  have halgebra (c t v a : ℂ) :
      c * (t * v / (baseVolume : ℂ)) - inverseNormalizer * (t * a) =
        inverseNormalizer * t * (c * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) * v) - a) := by
    simp only [allocatedProductIdealNormalizer, Complex.ofReal_mul]
    by_cases hN : (baseVolume : ℂ) = 0
    · simp only [hN, zero_mul, inv_zero, div_zero, mul_zero, zero_sub, neg_zero]
    · field_simp [hN, hV]
  have hsum : (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
      allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
        ∏ s, maskedSiteFactor
          (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
            fun j i => ((v.2 j () i).val : ZMod period))) label f k s
            (mixedCoveredRowsSiteValue rowSets d z s)) =
      inverseNormalizer * ((mask label : ℂ) * ∑ k, a k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s)) := by
    have hexp := maskedSiteExpansion_identity
      (fun (_ : Finset α) (v : MixedCoveredJetSource I (fun _ => Unit) E n d) =>
        (fun j i => ((v.1 j).2 i () : ZMod period), fun j i => ((v.2 j () i).val : ZMod period)))
      (fun label => (mask label : ℂ)) a f (mixedCoveredRowsSiteValue rowSets d z)
    change (∑ label, ∑ k, ((mask label : ℂ) * a k) * ∏ s, maskedSiteFactor
      (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
        fun j i => ((v.2 j () i).val : ZMod period))) label f k s
        (mixedCoveredRowsSiteValue rowSets d z s)) =
      (mask label : ℂ) * ∑ k, a k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s) at hexp
    rw [← hexp]
    simp only [allocatedProductMaskedIdealCoefficient, Finset.mul_sum, mul_assoc]
  rw [hsum, allocatedProductFullGridPrefactor_site_masks B U b S rowSets x y₀ q d period
    r hr hb o bW (D) hperiod z hz]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  rw [halgebra, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hmask (norm_nonneg _)) herr (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) hcap)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hperiod hM hm hR hC hchart hbudget in
theorem allocatedProductChartDensityApproximation_error {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (D : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ v : AllocatedLongJetRows B U b S rowTypes,
      ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D (allocatedLongJetRealCoordinates B U b S v) : ℂ) -
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets v s)‖ ≤ ε)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ D y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
      ‖inverseNormalizer‖ *
        (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * ε := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedProductChartIdealApproximation_eq_mixed B U b S rowSets x y₀ q d period r hr hb o bW
      hR C hC hchart hbudget a f z hz]
    apply allocatedProductPrefactor_masked_density_error B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR a
      (fun k s v => allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (f k s) (chart v)) D ε z hz
    have he := allocatedBufferedRowDensityProduct_error B U b S o hb bW d r hr rowSets
      hR C hC hchart hbudget a f D ε z hz (herr (split z.1).2)
    simpa only [mixedCoveredRowsSiteValue_chart] using he
  · rw [allocatedProductFullGridPrefactor_zero B U b S rowSets d r hr x hb o bW q y₀ D y hy,
      allocatedProductChartIdealApproximation_zero_outside B U b S rowSets x y₀ q d period r hr hb o bW
        hR C hC hchart hbudget a f y hy,
      sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _)
      (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _)
        (coefficientDeckPeriodCap_nonneg rowTypes E period))) hε

end Erdos3.VectorPolynomial

end

end OAI
