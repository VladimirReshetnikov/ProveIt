import OAI.Combinatorics.Progressions.Geometry.AllocatedMaskedChartProduct
import OAI.Combinatorics.Progressions.Probability.AllocatedReconstructedCutoffMass

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

noncomputable def allocatedProductChartIdealApproximation {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (y : EuclideanJetLayers U rowTypes) : ℂ :=
  ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
    allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
      ∏ s, allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period (label s) (f k s)
        (coveredRowsSiteValue rowSets U y s)

theorem allocatedProductChartIdealApproximation_measurable {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : ∀ k s, LipschitzWith L (f k s)) (hf1 : ∀ k s v, ‖f k s v‖ ≤ 1) :
    Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) := by
  unfold allocatedProductChartIdealApproximation
  apply Finset.measurable_sum
  intro label _
  apply Finset.measurable_sum
  intro k _
  apply measurable_const.mul
  apply Finset.measurable_prod
  intro s _
  apply (allocatedMaskedSiteChartFactor_measurable B U b S o hb bW d r hr period (label s) (f k s)
    (hf k s) (hf1 k s)).comp
  have hcont : Continuous (fun y : EuclideanJetLayers U rowTypes => coveredRowsSiteValue rowSets U y s) := by
    unfold coveredRowsSiteValue
    fun_prop
  exact hcont.measurable

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedProductChartIdealApproximation_eq_mixed {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f (chart z) =
      ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
          ∏ s, allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f label k s
            (mixedCoveredRowsSiteValue rowSets d z s) := by
  unfold allocatedProductChartIdealApproximation
  apply Finset.sum_congr rfl
  intro label _
  apply Finset.sum_congr rfl
  intro k _
  rw [allocatedMaskedChartProduct_eq_mixed B U b S o hb bW d r hr period rowSets hR C hC hchart hbudget f label k z hz]

include hR hC hchart hbudget in
theorem allocatedProductChartIdealApproximation_zero_outside {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (y : EuclideanJetLayers U rowTypes) (hy : y ∉ chart '' region) :
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y = 0 := by
  unfold allocatedProductChartIdealApproximation
  apply Finset.sum_eq_zero
  intro label _
  apply Finset.sum_eq_zero
  intro k _
  rw [allocatedMaskedChartProduct_zero_outside B U b S o hb bW d r hr period rowSets hR C hC hchart hbudget (f k) label y hy,
    mul_zero]

include hperiod hM hm hR hC hchart hbudget in
theorem exists_allocated_global_masked_ideal_approximation
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let sourceRadius : ℝ≥0 := allocatedProductIdealSiteRadius (G := G) B rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset α) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε := by
  intro sourceRadius cutoffLip Q A maskCap
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hcoeff, _hfactor, herr⟩ :=
    exists_allocated_product_masked_ideal_approximation B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget δ hδ hδ1 hε hp hbox hεp hδp
  refine ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hcoeff, ?_, ?_, ?_, ?_⟩
  · intro label i s y
    exact allocatedMaskedSiteChartFactor_norm B U b S o hb bW d r hr period label (f i s) (hf i s) y
  · intro label i s
    exact allocatedMaskedSiteChartFactor_measurable B U b S o hb bW d r hr period label (f i s) (hLf i s) (hf i s)
  · exact allocatedProductChartIdealApproximation_measurable B U b S rowSets x y₀ q d period r hr hb o bW a f hLf hf
  · intro y
    by_cases hy : y ∈ chart '' region
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [allocatedProductChartIdealApproximation_eq_mixed B U b S rowSets x y₀ q d period r hr hb o bW hR C hC hchart hbudget a f z hz]
      exact herr z hz
    · rw [allocatedProductFullGridPrefactor_zero B U b S rowSets d r hr x hb o bW q y₀
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y hy,
        allocatedProductChartIdealApproximation_zero_outside B U b S rowSets x y₀ q d period r hr hb o bW hR C hC hchart hbudget a f y hy,
        sub_self, norm_zero]
      exact mul_nonneg (mul_nonneg (norm_nonneg _)
        (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period))) hε.le

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
theorem exists_allocated_global_masked_ideal_approximation_cutoff
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let sourceRadius : ℝ≥0 := allocatedProductIdealSiteRadius (G := G) B rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset α) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * (‖cutoff y‖ * ε) := by
  intro sourceRadius cutoffLip Q A maskCap
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hcoeff, _hfactor, herr⟩ :=
    exists_allocated_product_masked_ideal_approximation_cutoff B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget δ hδ hδ1 hε hp hbox hεp hδp
  refine ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hcoeff, ?_, ?_, ?_, ?_⟩
  · intro label i s y
    exact allocatedMaskedSiteChartFactor_norm B U b S o hb bW d r hr period label (f i s) (hf i s) y
  · intro label i s
    exact allocatedMaskedSiteChartFactor_measurable B U b S o hb bW d r hr period label (f i s) (hLf i s) (hf i s)
  · exact allocatedProductChartIdealApproximation_measurable B U b S rowSets x y₀ q d period r hr hb o bW a f hLf hf
  · intro y
    by_cases hy : y ∈ chart '' region
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [allocatedProductChartIdealApproximation_eq_mixed B U b S rowSets x y₀ q d period r hr hb o bW hR C hC hchart hbudget a f z hz]
      exact herr z hz
    · rw [allocatedProductFullGridPrefactor_zero B U b S rowSets d r hr x hb o bW q y₀
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y hy,
        allocatedProductChartIdealApproximation_zero_outside B U b S rowSets x y₀ q d period r hr hb o bW hR C hC hchart hbudget a f y hy,
        sub_self, norm_zero]
      exact mul_nonneg (mul_nonneg (norm_nonneg _)
        (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period))) (mul_nonneg (norm_nonneg _) hε.le)

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
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
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

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

def AllocatedLongPhysicalExpansionIdentity (gl : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) → T → Finset (Fin dim) → LongSpace → ℂ) : Prop :=
  ∀ (v : X → (Unit ⊕ Fin dim) → ℤ),
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
      ∑ label, ∑ i, ((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * ∏ s, gl label i s (physicalMaskedFactorInput period p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))

def AllocatedGridPhysicalExpansionIdentity (gg : (∀ a, (e a).Term) → Finset (Fin dim) → GridSpace → ℂ) : Prop :=
  ∀ (v : X → (Unit ⊕ Fin dim) → ℤ),
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) * allocatedFullGridChartModel B U b S rowSets d hb o bW e
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) * ∑ k, coverSiteCoefficient e k * ∏ s, gg k s (physicalGridFactorInput (commonSitePeriod e k) p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))

def AllocatedModelPhysicalExpansionIdentity
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) → T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ) : Prop :=
  ∀ (v : X → (Unit ⊕ Fin dim) → ℤ),
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) * allocatedFullGridChartModel B U b S rowSets d hb o bW e
      (BooleanCubeKernel.physicalCubeRowSample U d rows p hm v) =
      ∑ label, ∑ i, ∑ k, (((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) * coverSiteCoefficient e k) *
        ∏ s, g label i k s (physicalMaskedFactorInput period p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)), physicalGridFactorInput (commonSitePeriod e k) p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))

theorem join_allocated_physical_expansions
    (gl : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) → T → Finset (Fin dim) → LongSpace → ℂ)
    (gg : (∀ a, (e a).Term) → Finset (Fin dim) → GridSpace → ℂ)
    {LL : ℝ≥0} {LG : (∀ a, (e a).Term) → ℝ≥0}
    (hgl : ∀ label i s, LipschitzWith LL (gl label i s))
    (hgg : ∀ k s, LipschitzWith (LG k) (gg k s))
    (hglb : ∀ label i s z, ‖gl label i s z‖ ≤ 1)
    (hggb : ∀ k s z, ‖gg k s z‖ ≤ 1)
    (hlong : AllocatedLongPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW a f p hm gl)
    (hgrid : AllocatedGridPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm gg) :
    ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) → T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ,
      (∀ label i k s, LipschitzWith (LL + LG k) (g label i k s)) ∧
      (∀ label i k s z, ‖g label i k s z‖ ≤ 1) ∧
      AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g := by
  obtain ⟨g, hgL, hgb, hgv⟩ := finiteNestedSiteExpansion_product_functions gl gg hgl hgg hglb hggb
  refine ⟨g, hgL, hgb, ?_⟩
  intro v
  exact hgv
    (fun label i => (2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) (coverSiteCoefficient e)
    (fun s => physicalMaskedFactorInput period p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))
    (fun k s => physicalGridFactorInput (commonSitePeriod e k) p (fun z => (BooleanCubeKernel.physicalCubeVertexValue v s z : ℝ)))
    _ _ (hlong v) (hgrid v)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period] (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))

variable {K : Type*} [Fintype K] (a : K → ℂ)
variable (f : K → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (v : X → (Unit ⊕ Fin dim) → ℤ)

include hp in
theorem allocatedProductChartIdealApproximation_physical :
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
      (physicalCubeRowSample U d rows p hm v) =
    ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
      allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
        ∏ s, allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period (label s) (f k s)
          (physicalSingleSiteValue U d p hm (fun z => (physicalCubeVertexValue v s z : ℝ))) := by
  unfold allocatedProductChartIdealApproximation
  simp_rw [coveredRowsSiteValue_physical U d p hm hp v]

include hp in
theorem allocatedProductPrefactor_physical_site_error (hR : ∀ j, 0 < R j) (δ : ℝ≥0) (error : ℝ)
    (herr : ∀ y : EuclideanJetLayers U rowTypes,
      ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
          (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
        allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤ error) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) (physicalCubeRowSample U d rows p hm v) -
      ∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
          ∏ s, allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period (label s) (f k s)
            (physicalSingleSiteValue U d p hm (fun z => (physicalCubeVertexValue v s z : ℝ)))‖ ≤ error := by
  rw [← allocatedProductChartIdealApproximation_physical B U b S x y₀ q d period r hr hb o bW a f p hp hm v]
  exact herr _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

structure AllocatedFiniteIdealData {m : ℕ} (α : Type*) (I : Fin m → Type*) (n : Fin m → ℕ) where
  size : ℕ
  coefficient : (Finset α × LayerSamplerAxis I n → Fin size) → ℂ
  factor : (Finset α × LayerSamplerAxis I n → Fin size) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ

abbrev AllocatedFiniteIdealData.Term {m : ℕ} {α : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
    (F : AllocatedFiniteIdealData α I n) := Finset α × LayerSamplerAxis I n → Fin F.size

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
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "r" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "hr" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j)

def AllocatedFiniteIdealData.Bounds (δ : ℝ≥0) (ε p M : ℝ) (F : AllocatedFiniteIdealData α I n) : Prop :=
    let sourceRadius : ℝ≥0 := allocatedProductIdealSiteRadius (G := G) B rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    (F.size : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card F.Term : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
        (∑ i, ‖F.coefficient i‖) ≤ A ∧
        (∀ i s v, ‖F.factor i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (F.factor i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → F.factor i s v = 0) ∧
        (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period F.coefficient label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset α) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (F.factor i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (F.factor i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW F.coefficient F.factor) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW F.coefficient F.factor y‖ ≤
            ‖inverseNormalizer‖ * maskCap * (‖cutoff y‖ * ε)

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

variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) *
    (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)))) ≤ 1 / 4)

include hperiod hM hm hC hchart hbudget in
theorem exists_allocated_finite_ideal_data
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    ∃ F : AllocatedFiniteIdealData α I n,
      F.Bounds B U b S rowSets x y₀ q d period hb o bW hR δ ε p M := by
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLip, hsupport, hcoeff, hfactor, hmeas, happrox, herr⟩ :=
    exists_allocated_global_masked_ideal_approximation_cutoff B U b S rowSets x y₀ q d period r hr
      hb o bW hperiod hM hm hR C hC hchart hbudget δ hδ hδ1 hε hp hbox hεp hδp
  exact ⟨⟨k, a, f⟩, hk, hcard, ha, hf, hLip, hsupport, hcoeff, hfactor, hmeas, happrox, herr⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem finiteProbability_weightedError_test_le {Ω : Type*} [Fintype Ω]
    (law : FiniteProbabilityWeights Ω) (error : Ω → ℂ) (D : Ω → ℝ)
    {c M : ℝ} (hc : 0 ≤ c) (hpoint : ∀ z, ‖error z‖ ≤ c * D z)
    (hD : law.mean D ≤ M) :
    law.mean (fun z => ‖error z‖) ≤ c * M ∧
    ∀ φ : Ω → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
      ‖law.complexMean (fun z => error z * φ z)‖ ≤ c * M := by
  have hmean : law.mean (fun z => ‖error z‖) ≤ c * M :=
    (law.mean_mono hpoint).trans ((law.mean_const_mul c D).le.trans
      (mul_le_mul_of_nonneg_left hD hc))
  refine ⟨hmean, ?_⟩
  intro φ hφ
  apply (law.norm_complexMean_le_mean_norm _).trans
  apply (law.mean_mono (g := fun z => ‖error z‖) _).trans hmean
  intro z
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hφ z) (norm_nonneg _)).trans_eq (mul_one _)

theorem selectedResidue_weightedError_test_le {K X : Type*} [Fintype K] [Fintype X]
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern K X stride))
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (error : (K × X → ℤ) → ℂ) (D : (K × X → ℤ) → ℝ)
    {c M : ℝ} (hc : 0 ≤ c) (hpoint : ∀ z, ‖error z‖ ≤ c * D z)
    (hD : selectedResidueDensityMass stride cells V D ≤ M) :
    selectedResidueDensityMass stride cells V (fun z => ‖error z‖) ≤ c * M ∧
    ∀ φ : (K × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
      ‖∑' z, ((selectedResidueSmoothPMF stride cells V hV hZ z).toReal : ℂ) *
        (error z * φ z)‖ ≤ c * M := by
  have hmean : (selectedResidueFiniteLaw stride cells V hV hZ).mean (fun z => D z.val) ≤ M := by
    rw [selectedResidueFiniteLaw_densityMass]
    exact hD
  obtain ⟨hbound, htest⟩ := finiteProbability_weightedError_test_le
    (selectedResidueFiniteLaw stride cells V hV hZ) (fun z => error z.val) (fun z => D z.val)
    hc (fun z => hpoint z.val) hmean
  rw [selectedResidueFiniteLaw_densityMass stride cells V hV hZ (fun z => ‖error z‖)] at hbound
  refine ⟨hbound, ?_⟩
  intro φ hφ
  have h := htest (fun z => φ z.val) (fun z => hφ z.val)
  rw [selectedResidueFiniteLaw_complexMean stride cells V hV hZ (fun z => error z * φ z)] at h
  exact h

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q : ℕ) (δ : ℝ≥0)

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "actual" => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
  (allocatedPhysicalLongIdeal B U b hR S rowSets δ)

theorem allocatedProductIdealError_sampled
    {X : Type*} [Fintype X]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride))
    (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
    (P : EuclideanJetLayers U rowTypes → ℂ) {A ε M : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (herr : ∀ y, ‖actual y - P y‖ ≤ amp * A * (‖cutoff y‖ * ε))
    (hcutoff : selectedResidueDensityMass stride cells V
      (fun z => amp * ‖cutoff (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))‖) ≤ M) :
    selectedResidueDensityMass stride cells V (fun z =>
      ‖actual (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)) -
        P (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))‖) ≤ (A * ε) * M ∧
    ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
      ‖∑' z, ((selectedResidueSmoothPMF stride cells V hV hZ z).toReal : ℂ) *
        ((actual (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)) -
          P (physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z))) * φ z)‖ ≤ (A * ε) * M := by
  let sample := fun z : Option (Fin dim) × X → ℤ => physicalCubeRowSample U d rows p hm (standardPhysicalCubeOutput z)
  let error := fun z => actual (sample z) - P (sample z)
  have hpoint (z : Option (Fin dim) × X → ℤ) : ‖error z‖ ≤ (A * ε) * (amp * ‖cutoff (sample z)‖) := by
    apply (herr (sample z)).trans_eq
    ring
  exact selectedResidue_weightedError_test_le stride cells V hV hZ error
    (fun z => amp * ‖cutoff (sample z)‖) (mul_nonneg hA hε) hpoint hcutoff

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
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

variable (hperiod : ∀ j, integerScalarLattice {t : Finset (Fin dim) // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset (Fin dim) // t ∈ rowSets j} → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hperiod hM hm hR hC hchart hbudget in
theorem exists_allocated_global_masked_ideal_approximation_sampled
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let sourceRadius : ℝ≥0 := allocatedProductIdealSiteRadius (G := G) B rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card (Fin dim)) p
    let A := Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin dim)) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * (‖cutoff y‖ * ε)) ∧
        ∀ {X : Type*} [Fintype X] (pPoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (hPoly : ∀ j e, coefficients (pPoly j) e ∈ U j)
          (stride : X → ℕ) (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride))
          (V : Option (Fin dim) × X → ℝ) (hV : ∀ z, 0 < V z)
          (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z) {T : ℝ},
          selectedResidueDensityMass stride cells V
            (fun z => ‖inverseNormalizer‖ * ‖cutoff (physicalCubeRowSample U d rows pPoly hPoly (standardPhysicalCubeOutput z))‖) ≤ T →
          selectedResidueDensityMass stride cells V
            (fun z => ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedPhysicalLongIdeal B U b hR S rowSets δ) (physicalCubeRowSample U d rows pPoly hPoly (standardPhysicalCubeOutput z)) - allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f (physicalCubeRowSample U d rows pPoly hPoly (standardPhysicalCubeOutput z))‖) ≤ (maskCap * ε) * T ∧
          ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
            ‖∑' z, ((selectedResidueSmoothPMF stride cells V hV hZ z).toReal : ℂ) *
              ((allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedPhysicalLongIdeal B U b hR S rowSets δ) (physicalCubeRowSample U d rows pPoly hPoly (standardPhysicalCubeOutput z)) - allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f (physicalCubeRowSample U d rows pPoly hPoly (standardPhysicalCubeOutput z))) * φ z)‖ ≤ (maskCap * ε) * T := by
  intro sourceRadius cutoffLip Q A maskCap
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hcoeff, hfactor, hmfactor, hP, herr⟩ :=
    exists_allocated_global_masked_ideal_approximation_cutoff B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget δ hδ hδ1 hε hp hbox hεp hδp
  refine ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hcoeff, hfactor, hmfactor, hP, herr, ?_⟩
  intro X _ pPoly hPoly stride cells V hV hZ T hcutoff
  exact allocatedProductIdealError_sampled B U b S rowSets o hb bW d r hr hR x y₀ q δ
    pPoly hPoly stride cells V hV hZ _
    (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period))
    hε.le herr hcutoff

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem finite_weighted_window_norm_mono {A V : Type*} [Fintype A]
    (weight : A → ℝ) (hweight : ∀ a, 0 ≤ weight a) (window : Finset V)
    (F G : A → V → ℂ) (volume : ℝ) (hvolume : 0 ≤ volume) {c : ℝ}
    (hpoint : ∀ a v, v ∈ window → ‖F a v‖ ≤ c * ‖G a v‖) :
    (∑ a, weight a * ((∑ v ∈ window, ‖F a v‖) / volume)) ≤
      c * ∑ a, weight a * ((∑ v ∈ window, ‖G a v‖) / volume) := by
  calc
    _ ≤ ∑ a, weight a * ((∑ v ∈ window, c * ‖G a v‖) / volume) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun v hv => hpoint a v hv)) hvolume)
        (hweight a)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum]
      ring

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable {X : Type*} [Fintype X]
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable (stride N : X → ℕ) (hs : ∀ t, 0 < stride t) (hN : ∀ t, 0 < N t)
variable (modulus : ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value) (base : X → ℤ)
variable {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "H" => trimmedSpatialRootScale τ N stride
local notation "T" => trimmedSpatialSlopeScale W τ N stride
local notation "envelope" => referenceJetEnvelopeWidths (q := dim) stride H
local notation "volume" => (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i)
local notation "factor" => ((30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
  (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X)
local notation "amp" => ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "point" => physicalCubeRowSample U d rows p hm
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus stride))

local notation "principalTuples" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S)

include hs hN hW hτ in
theorem allocatedProductIdealError_recentered_mass
    (hR : ∀ j, 0 < R j) (q : ℕ) (δ : ℝ≥0)
    (P : principalTuples → EuclideanJetLayers U rowTypes → ℂ)
    {A ε M ξ : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) (hξ : 0 < ξ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (hrows : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t)
    (hscale : ∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t)
    (href : ∀ cell : ColumnResiduePattern (Option (Fin dim)) X stride,
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride {cell} envelope z,
        selectedResidueDensityMass stride {cell} envelope
          (fun z => amp * ‖cutoff (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ M)
    (herr : ∀ y₀ y,
      ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P y₀ y‖ ≤ amp * A * (‖cutoff y‖ * ε)) :
    (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mean
      (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ) B U b S X modulus stride
        wholeReference x N base cells point
        (fun y₀ y => allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
          (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P y₀ y)) ≤ (A * ε) * (factor * M) := by
  let F : principalTuples → EuclideanJetLayers U rowTypes → ℂ := fun y₀ y =>
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
      (allocatedPhysicalLongIdeal B U b hR S rowSets δ) y - P y₀ y
  let cutoffF : principalTuples → EuclideanJetLayers U rowTypes → ℂ := fun _ y => ((amp * ‖cutoff y‖ : ℝ) : ℂ)
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
  have hpoint (y₀ : principalTuples) (y : EuclideanJetLayers U rowTypes) :
      ‖F y₀ y‖ ≤ (A * ε) * ‖cutoffF y₀ y‖ := by
    dsimp only [F, cutoffF]
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    apply (herr y₀ y).trans_eq
    ring
  have hvolume : 0 < volume := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim)
      (trimmedSpatial_scales_pos hW hτ N stride t (hN t) (hs t)).1
      (trimmedSpatial_scales_pos hW hτ N stride t (hN t) (hs t)).2
      (Nat.cast_pos.mpr S.positive) i))
  have hlocal (y₀ : principalTuples) :
      allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ) B U b S X modulus stride
        wholeReference x N base cells point F y₀ ≤
      (A * ε) * allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ) B U b S X modulus stride
        wholeReference x N base cells point cutoffF y₀ := by
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride wholeReference x base
      (principalResidueLabel (residueRefinedPeriod modulus stride) y₀)
    exact finite_weighted_window_norm_mono
      (fun a : cells => selectedResidueCellWeight stride cells V a)
      (fun a => selectedResidueCellWeight_nonneg stride cells V a) (spatialWindow H 4)
      (fun a v => F y₀ (point (reconstruct a.val v)))
      (fun a v => cutoffF y₀ (point (reconstruct a.val v))) volume hvolume.le
      (fun a v _ => hpoint y₀ (point (reconstruct a.val v)))
  have hmean := law.mean_mono hlocal
  rw [law.mean_const_mul] at hmean
  have hmass := allocatedNormalizedCutoff_recentered_mass B U b S rowSets o hb bW d r hr p hm
    stride N hs hN modulus wholeReference x base hW hτ hξ cells hZ hrows hscale href
  exact hmean.trans (mul_le_mul_of_nonneg_left hmass (mul_nonneg hA hε))

end Erdos3.BooleanCubeKernel

end

end OAI
