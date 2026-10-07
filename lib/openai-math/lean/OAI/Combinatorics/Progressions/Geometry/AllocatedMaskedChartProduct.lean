/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedCutoffMaskedIdeal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
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
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d quarter

noncomputable def mixedCoveredSiteResidue (w : MixedCoveredJetSource I single E n d) :
    (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period) :=
  (fun j i => ((w.1 j).2 i () : ZMod period), fun j i => ((w.2 j () i).val : ZMod period))

noncomputable def allocatedMaskedSiteChartFactor
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) : EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun w =>
    if mixedCoveredSiteResidue d period w = label then
      allocatedBufferedMixedSiteFactor B U b S r hr f (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())
    else 0)

theorem allocatedMaskedSiteChartFactor_apply
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    (w : MixedCoveredJetSource I single E n d) (hw : w ∈ region) :
    allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f (chart w) =
      if mixedCoveredSiteResidue d period w = label then
        allocatedBufferedSiteChartFactor B U b S o hb bW d r hr f (chart w) else 0 := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  simp only [allocatedMaskedSiteChartFactor, allocatedBufferedSiteChartFactor,
    restrictedComplexChartDensity_apply _ _ _ _ hinj hw, Complex.ofReal_one, one_mul]

theorem allocatedMaskedSiteChartFactor_norm
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (hf : ∀ v, ‖f v‖ ≤ 1)
    (y : EuclideanJetLayers U single) :
    ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y‖ ≤ 1 := by
  apply restrictedComplexChartDensity_norm_le chart region
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) _ zero_le_one
  intro w
  split_ifs
  · exact allocatedBufferedMixedSiteFactor_norm_le B U b S r hr f hf _
  · simp only [norm_zero, zero_le_one]

theorem allocatedMaskedSiteChartFactor_zero_of_cutoff_zero
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (y : EuclideanJetLayers U single)
    (hy : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) y = 0) :
    allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f y = 0 := by
  by_cases hmem : y ∈ chart '' region
  · obtain ⟨w, hw, rfl⟩ := hmem
    rw [allocatedMaskedSiteChartFactor_apply B U b S o hb bW d r hr period label f w hw]
    split_ifs
    · exact allocatedBufferedSiteChartFactor_zero_of_cutoff_zero B U b S o hb bW d r hr f _ hy
    · rfl
  · unfold allocatedMaskedSiteChartFactor
    exact restrictedComplexChartDensity_zero _ _ _ _ hmem

omit [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] in
theorem mixedCoveredSiteResidue_measurable [NeZero period] :
    Measurable (mixedCoveredSiteResidue (I := I) (E := E) (n := n) d period) := by
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro i
    exact (measurable_of_countable (fun z : ℤ => (z : ZMod period))).comp (by fun_prop)
  · apply Measurable.of_eval
    intro j
    apply Measurable.of_eval
    intro i
    exact (measurable_of_countable (fun z : ZMod d => (z.val : ZMod period))).comp (by fun_prop)

theorem allocatedMaskedSiteChartFactor_measurable [NeZero period]
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ v, ‖f v‖ ≤ 1) :
    Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f) := by
  apply mixedCoveredJet_restrictedComplexDensity_measurable U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
  have hset : MeasurableSet {w : MixedCoveredJetSource I single E n d | mixedCoveredSiteResidue d period w = label} :=
    (mixedCoveredSiteResidue_measurable (I := I) (E := E) (n := n) d period) (measurableSet_singleton label)
  have hbuf : Measurable (fun w : MixedCoveredJetSource I single E n d =>
      allocatedBufferedMixedSiteFactor B U b S r hr f (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())) := by
    let : ∀ j, BorelSpace ((I j → ℝ) × (Fin (n j) → ℤ)) := fun _ => inferInstance
    let : BorelSpace (∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) := Pi.borelSpace
    apply (allocatedBufferedMixedSiteFactor_continuous B U b S r hr f hf hf1).measurable.comp
    change Measurable (fun w : MixedCoveredJetSource I single E n d =>
      fun j => ((fun i => (w.1 j).1 i ()), (fun i => (w.1 j).2 i ())))
    fun_prop
  exact hbuf.ite hset measurable_const

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

omit [Fintype α] [DecidableEq α] in
theorem allocatedProductMaskedIdealSiteFactor_zero
    {K : Type*} (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
    (k : K) (s : Finset α) (w : MixedCoveredJetSource I (fun _ => Unit) E n d)
    (hw : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1) (chart w) = 0) :
    allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f label k s w = 0 := by
  unfold allocatedProductMaskedIdealSiteFactor maskedSiteFactor
  dsimp only
  rw [allocatedBufferedSiteChartFactor_zero_of_cutoff_zero B U b S o hb bW d r hr (f k s) _ hw]
  split_ifs <;> rfl

theorem allocatedMaskedChartProduct_zero_of_cutoff_zero
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
    (y : EuclideanJetLayers U rowTypes) (hy : cutoff y = 0) :
    (∏ s, allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period (label s) (f s)
      (coveredRowsSiteValue rowSets U y s)) = 0 := by
  change (∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
    (coveredRowsSiteValue rowSets U y s)) = 0 at hy
  obtain ⟨s, hs, hsite⟩ := Finset.prod_eq_zero_iff.mp hy
  exact Finset.prod_eq_zero hs
    (allocatedMaskedSiteChartFactor_zero_of_cutoff_zero B U b S o hb bW d r hr period (label s) (f s) _ hsite)

theorem allocatedMaskedMixedProduct_zero_of_cutoff_zero
    {K : Type*} (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
    (k : K) (z : MixedCoveredJetSource I rowTypes E n d) (hz : cutoff (chart z) = 0) :
    (∏ s, allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f label k s
      (mixedCoveredRowsSiteValue rowSets d z s)) = 0 := by
  change (∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
    (coveredRowsSiteValue rowSets U (chart z) s)) = 0 at hz
  obtain ⟨s, hs, hsite⟩ := Finset.prod_eq_zero_iff.mp hz
  refine Finset.prod_eq_zero hs (allocatedProductMaskedIdealSiteFactor_zero B U b S o hb bW d r hr period f label k s _ ?_)
  simpa only [mixedCoveredRowsSiteValue_chart] using hsite

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedMaskedChartProduct_eq_mixed
    {K : Type*} (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
    (k : K) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    (∏ s, allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period (label s) (f k s)
      (coveredRowsSiteValue rowSets U (chart z) s)) =
    ∏ s, allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f label k s
      (mixedCoveredRowsSiteValue rowSets d z s) := by
  by_cases hc : cutoff (chart z) = 0
  · rw [allocatedMaskedChartProduct_zero_of_cutoff_zero B U b S o hb bW d r hr period rowSets (f k) label _ hc,
      allocatedMaskedMixedProduct_zero_of_cutoff_zero B U b S o hb bW d r hr period rowSets f label k z hc]
  · have hsites := allocatedProductSiteCutoff_sites_quarter B U b S rowSets o hb bW d r hr
      hR C hC hchart hbudget z hz hc
    apply Finset.prod_congr rfl
    intro s _
    rw [← mixedCoveredRowsSiteValue_chart rowSets U o b hb bW d z s,
      allocatedMaskedSiteChartFactor_apply B U b S o hb bW d r hr period (label s) (f k s) _ (hsites s)]
    simp only [mixedCoveredSiteResidue, allocatedProductMaskedIdealSiteFactor, maskedSiteFactor]
    split_ifs with hlabel <;> simp_all

include hR hC hchart hbudget in
theorem allocatedMaskedChartProduct_zero_outside
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)))
    (y : EuclideanJetLayers U rowTypes) (hy : y ∉ chart '' region) :
    (∏ s, allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period (label s) (f s)
      (coveredRowsSiteValue rowSets U y s)) = 0 := by
  apply allocatedMaskedChartProduct_zero_of_cutoff_zero B U b S o hb bW d r hr period rowSets f label y
  apply allocatedProductSiteCutoff_zero_outside B U b S rowSets o hb bW d r hr hR C hC hchart _ y hy
  intro j
  have hn : 0 ≤ (Fintype.card (Finset α) : ℝ) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j))) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC j)
      (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le)))
  have hb := hbudget j
  nlinarith [Nat.cast_nonneg (α := ℝ) (rowSets j).card]

end Erdos3.VectorPolynomial

end

end OAI
