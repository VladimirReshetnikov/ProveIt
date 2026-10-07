/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedProductPrefactorMasks
import OAI.Combinatorics.Progressions.Estimates.PreparedUniformEarlyRadiusWithCutoff
import OAI.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (rowSets : Fin m → Finset (Finset α))

local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "siteRadius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

theorem allocatedRowIdealCutoff_complex_mul (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ a, |v a| ≤ (siteRadius : ℝ)) → χ v = 1)
    (z : AllocatedLongJetRows B U b S jets) :
    (∏ s : Finset α, (χ (allocatedRowIdealCoordinates B U b S rowSets z s) : ℂ)) *
      (allocatedPhysicalLongIdeal B U b hR S rowSets δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) =
      (allocatedPhysicalLongIdeal B U b hR S rowSets δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) := by
  by_cases hz : allocatedPhysicalLongIdeal B U b hR S rowSets δ
      (allocatedLongJetRealCoordinates B U b S z) = 0
  · rw [hz, Complex.ofReal_zero, mul_zero]
  · have hp : (∏ s : Finset α, (χ (allocatedRowIdealCoordinates B U b S rowSets z s) : ℂ)) = 1 := by
      apply Finset.prod_eq_one
      intro s _
      rw [hone _ (allocatedRowIdealCoordinates_bound B U b S rowSets hR δ hδ hδ1 z hz s),
        Complex.ofReal_one]
    rw [hp, one_mul]

theorem allocatedRowIdealApproximation_error {T : Type*} [Fintype T]
    (hR : ∀ j, 0 < R j) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ a, |v a| ≤ (siteRadius : ℝ)) → χ v = 1)
    (a : T → ℂ) (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) (ε : ℝ)
    (herr : ∀ v : Finset α → LayerSamplerAxis I n → ℝ,
      ‖(∏ s, (χ (v s) : ℂ)) * (activeAveragedProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
          (fun a => (Subtype.val : jets a.val.1 → Finset α)) δ
          (booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
            (fun s d => v s d.val)) : ℂ) - ∑ i, a i * ∏ s, f i s (v s)‖ ≤ ε)
    (z : AllocatedLongJetRows B U b S jets) :
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
    ‖(volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
      ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)‖ ≤ ε ∧
    ‖(physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α))
        (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
      (∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ ≤ ε / volume := by
  intro volume
  have hdensity := congrArg Complex.ofReal (allocatedRowIdealCoordinates_density B U b S rowSets hR δ z)
  simp only [Complex.ofReal_mul] at hdensity
  have hcutoff := allocatedRowIdealCutoff_complex_mul B U b S rowSets hR δ hδ hδ1 χ hone z
  dsimp only [allocatedPhysicalLongIdeal] at hdensity hcutoff
  have hpoint := herr (allocatedRowIdealCoordinates B U b S rowSets z)
  rw [← hdensity] at hpoint
  have hproduct : (∏ s : Finset α, (χ (allocatedRowIdealCoordinates B U b S rowSets z s) : ℂ)) *
      ((volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α)) (fun a => R a.1) (fun a => hR a.1) δ
        (allocatedLongJetRealCoordinates B U b S z) : ℂ)) =
      (volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
        (fun a => (Subtype.val : jets a.val.1 → Finset α)) (fun a => R a.1) (fun a => hR a.1) δ
        (allocatedLongJetRealCoordinates B U b S z) : ℂ) := by
    rw [mul_left_comm, hcutoff]
  rw [hproduct] at hpoint
  refine ⟨hpoint, ?_⟩
  have hvolume : 0 < volume := Finset.prod_pos (fun q _ => hR q.1.val.1)
  have hvolumeC : (volume : ℂ) ≠ 0 := by exact_mod_cast hvolume.ne'
  calc
    _ = ‖((volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
          (fun a => (Subtype.val : jets a.val.1 → Finset α)) (fun a => R a.1) (fun a => hR a.1) δ
          (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
        ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ := by
      congr 1
      field_simp [hvolumeC]
    _ = _ := by rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvolume]
    _ ≤ _ := div_le_div_of_nonneg_right hpoint hvolume.le

theorem exists_allocated_row_ideal_site_approximation (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (siteRadius : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let radius : ℝ≥0 := allocatedProductIdealSiteRadius (G := G) B rowSets
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) (Fintype.card α) p
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + C) (f i s)) ∧
        (∀ i s v, (∃ d, 2 * (radius : ℝ) < |v d|) → f i s v = 0) ∧
        ∀ z : AllocatedLongJetRows B U b S jets,
          ‖(volume : ℂ) * (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
              (fun a => (Subtype.val : jets a.val.1 → Finset α))
              (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)‖ ≤ ε ∧
          ‖(physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
              (fun a => (Subtype.val : jets a.val.1 → Finset α))
              (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            (∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ ≤ ε / volume := by
  intro radius C Q volume
  obtain ⟨χ, hone, k, hk, hcard, a, f, ha, hf, hLf, hfsupport, herr⟩ :=
    exists_normalized_active_ideal_site_approximation (G := G) (Z := G × Option α) (B := B)
      (O := fun a : LayerSamplerAxis I n => jets a.1)
      hLayer grid (fun a => (Subtype.val : jets a.val.1 → Finset α)) δ hδ
      radius (allocatedProductIdealSiteRadius_pos B rowSets) hε hp hbox hεp hδp
  let alternateUniverse : Finset (Finset α × LayerSamplerAxis I n → Fin k) :=
    @Finset.univ _ (@Pi.instFintype (Finset α × LayerSamplerAxis I n) (fun _ => Fin k)
      (@instDecidableEqProd (Finset α) (LayerSamplerAxis I n) inferInstance
        (fun a b => Classical.propDecidable (a = b)))
      inferInstance (fun _ => Fin.fintype k))
  have huniv : (Finset.univ : Finset (Finset α × LayerSamplerAxis I n → Fin k)) =
      alternateUniverse := by
    ext i
    simp only [alternateUniverse, Finset.mem_univ]
  have hcard' : (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) := by
    simpa only [Q, Fintype.card_eq_nat_card] using hcard
  refine ⟨k, hk, hcard', a, f, ?_, hf, ?_, hfsupport, ?_⟩
  · calc
      (∑ i, ‖a i‖) = alternateUniverse.sum (fun i => ‖a i‖) := by rw [huniv]
      _ ≤ _ := ha
  · simpa only [Q] using hLf
  · intro z
    refine allocatedRowIdealApproximation_error B U b S rowSets hR δ hδ hδ1 χ hone a f ε ?_ z
    intro v
    rw [huniv]
    exact herr v

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
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)
local notation "siteChart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "siteRegion" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "factor" => allocatedBufferedSiteChartFactor B U b S o hb bW d r hr

theorem allocatedBufferedSiteChartFactor_on_chart
    (f : (LayerSamplerAxis I n → ℝ) → ℂ)
    (w : MixedCoveredJetSource I single E n d) (hw : w ∈ siteRegion) :
    factor f (siteChart w) = factor (fun _ => 1) (siteChart w) *
      f (allocatedNormalizedMixedSiteValue B U b S (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  simp only [allocatedBufferedSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _ hinj hw,
    Complex.ofReal_one, one_mul, allocatedBufferedMixedSiteFactor, bufferedCoordinateProjection,
    allocatedFullMixedSiteValue_projection, mul_one]

theorem allocatedBufferedSiteChartFactor_zero_of_cutoff_zero
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) (y : EuclideanJetLayers U single)
    (hy : factor (fun _ => 1) y = 0) : factor f y = 0 := by
  by_cases hmem : y ∈ siteChart '' siteRegion
  · obtain ⟨w, hw, rfl⟩ := hmem
    rw [allocatedBufferedSiteChartFactor_on_chart B U b S o hb bW d r hr f w hw, hy, zero_mul]
  · unfold allocatedBufferedSiteChartFactor
    exact restrictedComplexChartDensity_zero _ _ _ _ hmem

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
theorem allocatedBufferedRowIdealProduct
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    (∏ s, factor (f s) (coveredRowsSiteValue rowSets U (chart z) s)) =
      cutoff (chart z) * ∏ s, f s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s) := by
  by_cases hzero : cutoff (chart z) = 0
  · rw [hzero, zero_mul]
    change (∏ s, factor (fun _ => 1) (coveredRowsSiteValue rowSets U (chart z) s)) = 0 at hzero
    obtain ⟨s, hs, hsite⟩ := Finset.prod_eq_zero_iff.mp hzero
    exact Finset.prod_eq_zero hs
      (allocatedBufferedSiteChartFactor_zero_of_cutoff_zero B U b S o hb bW d r hr (f s) _ hsite)
  · have hsites := allocatedProductSiteCutoff_sites_quarter B U b S rowSets o hb bW d r hr
      hR C hC hchart hbudget z hz hzero
    calc
      _ = ∏ s, factor (fun _ => 1) (coveredRowsSiteValue rowSets U (chart z) s) *
          f s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s) := by
        apply Finset.prod_congr rfl
        intro s _
        rw [← mixedCoveredRowsSiteValue_chart rowSets U o b hb bW d z s,
          allocatedBufferedSiteChartFactor_on_chart B U b S o hb bW d r hr (f s) _ (hsites s),
          allocatedRowIdealCoordinates_mixed_value B U b S rowSets d z s]
      _ = _ := Finset.prod_mul_distrib

include hR hC hchart hbudget in
theorem allocatedBufferedRowIdealProduct_error {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (δ : ℝ≥0) (ε : ℝ) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (herr : ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ) -
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s)‖ ≤ ε) :
    ‖cutoff (chart z) * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ
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

include hR hC hchart hbudget in
theorem exists_allocated_buffered_row_ideal_approximation
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let sourceRadius : ℝ≥0 := allocatedProductIdealSiteRadius (G := G) B rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ d, 2 * (sourceRadius : ℝ) < |v d|) → f i s v = 0) ∧
        (∀ i s, Measurable (factor (f i s))) ∧
        (∀ i s y, ‖factor (f i s) y‖ ≤ 1) ∧
        ∀ z : MixedCoveredJetSource I rowTypes E n d, z ∈ region →
          ‖cutoff (chart z) * ((volume : ℂ) *
              (allocatedPhysicalLongIdeal B U b hR S rowSets δ
                (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
            ∑ i, a i * ∏ s, factor (f i s) (coveredRowsSiteValue rowSets U (chart z) s)‖ ≤ ε := by
  intro sourceRadius cutoffLip Q volume
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hsupport, herr⟩ :=
    exists_allocated_row_ideal_site_approximation B U b S rowSets hR δ hδ hδ1 hε hp hbox hεp hδp
  refine ⟨k, hk, hcard, a, f, ha, hf, hLf, hsupport, ?_, ?_, ?_⟩
  · intro i s
    exact allocatedBufferedSiteChartFactor_measurable B U b S o hb bW d r hr (f i s) (hLf i s) (hf i s)
  · intro i s y
    exact allocatedBufferedSiteChartFactor_norm_le B U b S o hb bW d r hr (f i s) (hf i s) y
  · intro z hz
    apply allocatedBufferedRowIdealProduct_error B U b S o hb bW d r hr rowSets hR C hC hchart hbudget a f δ ε z hz
    simpa only [allocatedPhysicalLongIdeal] using (herr (split z.1).2).1

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
theorem allocatedBufferedRowIdealProduct_error_cutoff {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (δ : ℝ≥0) (ε : ℝ) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (herr : ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ) -
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s)‖ ≤ ε) :
    ‖cutoff (chart z) * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
      ∑ k, a k * ∏ s, factor (f k s) (coveredRowsSiteValue rowSets U (chart z) s)‖ ≤ ‖cutoff (chart z)‖ * ε := by
  have hsum : (∑ k, a k * ∏ s, factor (f k s) (coveredRowsSiteValue rowSets U (chart z) s)) =
      cutoff (chart z) *
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s) := by
    simp_rw [allocatedBufferedRowIdealProduct B U b S o hb bW d r hr rowSets hR C hC hchart hbudget _ z hz]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left herr (norm_nonneg _)

include hR hC hchart hbudget in
theorem exists_allocated_buffered_row_ideal_approximation_cutoff
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let sourceRadius : ℝ≥0 := allocatedProductIdealSiteRadius (G := G) B rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ d, 2 * (sourceRadius : ℝ) < |v d|) → f i s v = 0) ∧
        (∀ i s, Measurable (factor (f i s))) ∧
        (∀ i s y, ‖factor (f i s) y‖ ≤ 1) ∧
        ∀ z : MixedCoveredJetSource I rowTypes E n d, z ∈ region →
          ‖cutoff (chart z) * ((volume : ℂ) *
              (allocatedPhysicalLongIdeal B U b hR S rowSets δ
                (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
            ∑ i, a i * ∏ s, factor (f i s) (coveredRowsSiteValue rowSets U (chart z) s)‖ ≤ ‖cutoff (chart z)‖ * ε := by
  intro sourceRadius cutoffLip Q volume
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hsupport, herr⟩ :=
    exists_allocated_row_ideal_site_approximation B U b S rowSets hR δ hδ hδ1 hε hp hbox hεp hδp
  refine ⟨k, hk, hcard, a, f, ha, hf, hLf, hsupport, ?_, ?_, ?_⟩
  · intro i s
    exact allocatedBufferedSiteChartFactor_measurable B U b S o hb bW d r hr (f i s) (hLf i s) (hf i s)
  · intro i s y
    exact allocatedBufferedSiteChartFactor_norm_le B U b S o hb bW d r hr (f i s) (hf i s) y
  · intro z hz
    apply allocatedBufferedRowIdealProduct_error_cutoff B U b S o hb bW d r hr rowSets hR C hC hchart hbudget a f δ ε z hz
    simpa only [allocatedPhysicalLongIdeal] using (herr (split z.1).2).1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

section Extraction

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
variable {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable (rowSets : Fin m → Finset (Finset α)) (d : ℕ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "single" => (fun _ : Fin m => Unit)

variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d]

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

theorem mixedCoveredRowsOfSites_chart_value
    (y : EuclideanJetLayers U rowTypes)
    (w : Finset α → MixedCoveredJetSource I single E n d)
    (hw : ∀ s, chart (w s) = coveredRowsSiteValue rowSets U y s) :
    chart (mixedCoveredRowsOfSites rowSets d w) = y := by
  funext j t
  rw [mixedCoveredRowsOfSites, mixedCoveredJetIntegerImage_chart]
  change (∑ s : Finset α, booleanJetExtractionMatrix Subtype.val t s • chart (w s) j ()) = _
  simp only [hw, coveredRowsSiteValue]
  exact rowRestrictedReconstruction_zsmul_inverse (rowSets j) (y j) t

end Extraction

section Cutoff

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "siteChart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "siteRegion" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "pointCap" => (fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))

local notation "rowRegion" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

variable (hrow : ∀ j, Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j))) ≤ 1 / 4)

include hR hC hchart hrow in
theorem allocatedProductSiteCutoff_mem_chart
    (y : EuclideanJetLayers U rowTypes)
    (hne : allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y ≠ 0) :
    y ∈ chart '' rowRegion := by
  obtain ⟨w, hw, hp⟩ := allocatedProductSiteCutoff_small_representatives B U b S rowSets o hb bW d r hr
    hR C hC hchart y hne
  refine ⟨mixedCoveredRowsOfSites rowSets d w, ?_,
    mixedCoveredRowsOfSites_chart_value rowSets d U o b hb bW y w hw⟩
  intro j _ t _
  refine ⟨?_, Set.mem_univ _⟩
  intro i
  have hc : ∀ j, 0 ≤ pointCap j := fun j =>
    mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))
  have hn := (mixedCoveredRowsOfSites_point_bound rowSets d U o b w pointCap hc hp j t).trans (hrow j)
  exact (PiLp.norm_apply_le (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
    (mixedCoveredJetCoordinates U o d (mixedCoveredRowsOfSites rowSets d w) j t).1) i).trans hn

include hR hC hchart hrow in
theorem allocatedProductSiteCutoff_zero_outside
    (y : EuclideanJetLayers U rowTypes) (hy : y ∉ chart '' rowRegion) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y = 0 := by
  by_contra hn
  exact hy (allocatedProductSiteCutoff_mem_chart B U b S rowSets o hb bW d r hr hR C hC hchart hrow y hn)

include hR hC hchart hrow in
theorem allocatedBufferedSiteProduct_zero_outside
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (y : EuclideanJetLayers U rowTypes) (hy : y ∉ chart '' rowRegion) :
    (∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (f s)
      (coveredRowsSiteValue rowSets U y s)) = 0 := by
  have hzero := allocatedProductSiteCutoff_zero_outside B U b S rowSets o hb bW d r hr hR C hC hchart hrow y hy
  change (∏ s, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
    (coveredRowsSiteValue rowSets U y s)) = 0 at hzero
  obtain ⟨s, hs, hsite⟩ := Finset.prod_eq_zero_iff.mp hzero
  exact Finset.prod_eq_zero hs
    (allocatedBufferedSiteChartFactor_zero_of_cutoff_zero B U b S o hb bW d r hr (f s) _ hsite)

end Cutoff
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

noncomputable def allocatedProductIdealNormalizer : ℝ := baseVolume * (∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ)

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

noncomputable def allocatedProductMaskedIdealCoefficient {K : Type*}
    (a : K → ℂ) (label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) (k : K) : ℂ :=
  inverseNormalizer * (mask label : ℂ) * a k

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
theorem allocatedProductMaskedIdealCoefficient_bound {K : Type*} [Fintype K]
    (a : K → ℂ) {A : ℝ} (ha : (∑ k, ‖a k‖) ≤ A) :
    (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
      ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k‖) ≤
      ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset α) *
        (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * A) := by
  have h := allocatedClippedPrefactorSiteMask_coefficient_sum (E := E) B U b S rowSets x y₀ q d period hperiod hM hm a ha
  calc
    _ = ‖inverseNormalizer‖ * ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k, ‖(mask label : ℂ) * a k‖ := by
      simp only [allocatedProductMaskedIdealCoefficient, norm_mul, Finset.mul_sum, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (norm_nonneg _)

include hperiod hM hm in
theorem allocatedProductPrefactor_masked_error (hR : ∀ j, 0 < R j)
    {K : Type*} [Fintype K] (a : K → ℂ)
    (f : K → Finset α → MixedCoveredJetSource I (fun _ => Unit) E n d → ℂ)
    (δ : ℝ≥0) (ε : ℝ) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (herr : ‖cutoff (chart z) * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
      ∑ k, a k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s)‖ ≤ ε) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (allocatedPhysicalLongIdeal B U b hR S rowSets δ) (chart z) -
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
    r hr hb o bW (allocatedPhysicalLongIdeal B U b hR S rowSets δ) hperiod z hz]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  rw [halgebra, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hmask (norm_nonneg _)) herr (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) hcap)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
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

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "naturalVolume" => allocatedFullGridNaturalVolume B U b S rowSets
local notation "gridScale" => allocatedGridJetScale B U b S (O := rowTypes)
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)
local notation "radiusVolume" => (∏ t : (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a))), R (Sigma.fst (Subtype.val (Sigma.fst t))))

omit [Fintype α] [DecidableEq α] in
theorem allocatedGridJetScale_natural_ratio :
    gridScale / naturalVolume = ∏ a : {a // grid a},
      (allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2) ^
        Fintype.card (rowTypes a.val.1) := by
  unfold allocatedGridJetScale allocatedFullGridNaturalVolume
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · simp only [allocatedGridAxisScale, allocatedGridNaturalScale, allocatedGridIntegerAxis,
      allocatedPrincipalChartRatio, Fintype.card_coe, div_pow, NNReal.coe_natCast]
    norm_cast

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hR : ∀ j, 0 < R j)

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_pos :
    0 < allocatedProductIdealNormalizer B U b S rowSets := by
  exact mul_pos (mul_pos (mul_pos (allocatedFullGridNaturalVolume_pos B U b hR S rowSets)
    (coveredJetArrayScale_pos U))
    (Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)))
    (Finset.prod_pos (fun t _ => hR (Sigma.fst (Subtype.val (Sigma.fst t)))))

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_inv_eq :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ =
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (rowTypes j)) *
      (∏ a : {a // grid a},
        allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2 ^
          Fintype.card (rowTypes a.val.1)) * radiusVolume⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg
    (allocatedProductIdealNormalizer_pos B U b S rowSets hR).le]
  rw [← allocatedGridJetScale_natural_ratio B U b S rowSets,
    ← allocatedGridLongJetScale_covolume B U b S (O := rowTypes)]
  have hg := (allocatedGridJetScale_pos B U b S (O := rowTypes)).ne'
  have hn := (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).ne'
  have hl : longScale ≠ 0 := (Finset.prod_pos
    (fun a _ => allocatedLongJetOutputScale_pos B U b S a)).ne'
  have hc := (coveredJetArrayScale_pos (O := rowTypes) U).ne'
  have hr : radiusVolume ≠ 0 := (Finset.prod_pos (fun t _ => hR (Sigma.fst (Subtype.val (Sigma.fst t))))).ne'
  unfold allocatedProductIdealNormalizer
  field_simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
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

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "naturalVolume" => allocatedFullGridNaturalVolume B U b S rowSets
local notation "gridScale" => allocatedGridJetScale B U b S (O := rowTypes)
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)
local notation "radiusVolume" => (∏ t : (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a))), R (Sigma.fst (Subtype.val (Sigma.fst t))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hR : ∀ j, 0 < R j)

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_inv_le (V : Fin m → ℝ)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {Q κ : ℝ} (hQ : 1 ≤ Q) (hκ0 : 0 ≤ κ) (hκ : ∀ j, (R j)⁻¹ ≤ κ)
    (hslots : ∀ j i, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Q) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      (∏ j, V j ^ Fintype.card (rowTypes j)) *
        (Q * κ) ^ Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) := by
  have hV0 (j) : 0 ≤ V j := (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le.trans (hV j)
  have hbase : 0 ≤ Q * κ := mul_nonneg (zero_le_one.trans hQ) hκ0
  have hg0 : 0 ≤ ∏ a : {a // grid a},
      allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2 ^
        Fintype.card (rowTypes a.val.1) :=
    Finset.prod_nonneg (fun a _ => pow_nonneg (allocatedPrincipalChartRatio_pos B U b hR _ _).le _)
  have hl0 : 0 ≤ radiusVolume⁻¹ := inv_nonneg.mpr (Finset.prod_nonneg (fun t _ => (hR (Sigma.fst (Subtype.val (Sigma.fst t)))).le))
  have hgrid : (∏ a : {a // grid a},
      allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2 ^
        Fintype.card (rowTypes a.val.1)) ≤
      ∏ a : {a // grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1) := by
    apply Finset.prod_le_prod₀
    · intro a _
      exact pow_nonneg (allocatedPrincipalChartRatio_pos B U b hR _ _).le _
    · intro a _
      apply pow_le_pow_left₀ (allocatedPrincipalChartRatio_pos B U b hR _ _).le
      apply (allocatedPrincipalChartRatio_le B U b hR _ _).trans
      rw [div_eq_mul_inv]
      exact mul_le_mul (hslots _ _) (hκ _) (inv_nonneg.mpr (hR _).le) (zero_le_one.trans hQ)
  have hlong : radiusVolume⁻¹ ≤
      ∏ a : {a // ¬grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1) := by
    simp only [Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, ← Finset.prod_inv_distrib, ← inv_pow]
    apply Finset.prod_le_prod₀
    · intro a _
      exact pow_nonneg (inv_nonneg.mpr (hR a.val.1).le) _
    · intro a _
      apply pow_le_pow_left₀ (inv_nonneg.mpr (hR a.val.1).le)
      exact (hκ a.val.1).trans (le_mul_of_one_le_left hκ0 hQ)
  have hcov : (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^
      Fintype.card (rowTypes j)) ≤ ∏ j, V j ^ Fintype.card (rowTypes j) := by
    apply Finset.prod_le_prod₀
    · intro j _
      exact pow_nonneg (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le _
    · intro j _
      exact pow_le_pow_left₀ (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le (hV j) _
  rw [allocatedProductIdealNormalizer_inv_eq B U b S rowSets hR, mul_assoc]
  calc
    _ ≤ (∏ j, V j ^ Fintype.card (rowTypes j)) *
        ((∏ a : {a // grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1)) *
          ∏ a : {a // ¬grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1)) :=
      mul_le_mul hcov
        (mul_le_mul hgrid hlong hl0 (Finset.prod_nonneg (fun a _ => pow_nonneg hbase _)))
        (mul_nonneg hg0 hl0) (Finset.prod_nonneg (fun j _ => pow_nonneg (hV0 j) _))
    _ = _ := by
      rw [Fintype.prod_subtype_mul_prod_subtype grid
        (fun a : LayerSamplerAxis I n => (Q * κ) ^ Fintype.card (rowTypes a.1)),
        Finset.prod_pow_eq_pow_sum, Fintype.card_sigma]

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_inv_le_exp {P : ℝ} (hP : 0 ≤ P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P)
    (hκ : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hslots : ∀ j i, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Real.exp P) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp (((∑ j, Fintype.card (rowTypes j) : ℕ) : ℝ) * P +
        (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) : ℝ) * (2 * P)) := by
  have h := allocatedProductIdealNormalizer_inv_le B U b S rowSets hR (fun _ => Real.exp P) hV
    (Real.one_le_exp hP) (Real.exp_pos P).le hκ hslots
  apply h.trans_eq
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

noncomputable def allocatedCanonicalNormalizerLog {A : Type*} [Semiring A]
    (m : ℕ) (D p g : A) : A :=
  (D ^ 2 + 2 * D) * (D + g + allocatedCommonProductRadiusLog m p g + 8)

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})

theorem allocatedCanonicalIdealNormalizer_pre_bound {D p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g)
    (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hRadius : ∀ j, R j = allocatedCommonProductRadius m p g)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp g) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp (allocatedCanonicalNormalizerLog m D p g) := by
  rcases hgeom with ⟨hD, hm, _, _, _, _, _, hout, hrows, hcoeff, _⟩
  have hradius := allocatedCommonProductRadius_bounds m hp hg
  have hR (j : Fin m) : 0 < R j := by rw [hRadius j]; exact hradius.2.1
  let P := D + g + allocatedCommonProductRadiusLog m p g + 8
  have hP : 0 ≤ P := by dsimp [P]; linarith only [hD, hg, hradius.1]
  have hV' (j : Fin m) : mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P :=
    (hV j).trans (Real.exp_le_exp.mpr (by dsimp [P]; linarith only [hD, hradius.1]))
  have hκ (j : Fin m) : (R j)⁻¹ ≤ Real.exp P := by
    rw [hRadius j, hradius.2.2.2.1]
    exact Real.exp_le_exp.mpr (by dsimp [P]; linarith only [hD, hg])
  have hslots (j : Fin m) (i : Fin (n j)) :
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Real.exp P := by
    have hc : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D :=
      (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hcoeff j)
    calc
      _ ≤ 8 * (D + 1) := by linarith only [hc]
      _ ≤ 8 * Real.exp D := mul_le_mul_of_nonneg_left (Real.add_one_le_exp D) (by norm_num)
      _ ≤ Real.exp 8 * Real.exp D := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8) (Real.exp_pos _).le
      _ = Real.exp (D + 8) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [P]; linarith only [hg, hradius.1])
  have hsum : ((∑ j, Fintype.card (rowTypes j) : ℕ) : ℝ) ≤ D ^ 2 := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ _j : Fin m, D := Finset.sum_le_sum (fun j _ => hrows j)
      _ = (m : ℝ) * D := by simp
      _ ≤ D * D := mul_le_mul_of_nonneg_right hm hD
      _ = D ^ 2 := by ring
  have hbound := allocatedProductIdealNormalizer_inv_le_exp B U b S rowSets hR hP hV' hκ hslots
  have hcost : ((∑ j, Fintype.card (rowTypes j) : ℕ) : ℝ) * P +
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) * (2 * P) ≤
      allocatedCanonicalNormalizerLog m D p g := by
    calc
      _ ≤ D ^ 2 * P + D * (2 * P) := add_le_add
        (mul_le_mul_of_nonneg_right hsum hP)
        (mul_le_mul_of_nonneg_right hout (mul_nonneg (by norm_num) hP))
      _ = allocatedCanonicalNormalizerLog m D p g := by
        dsimp only [P, allocatedCanonicalNormalizerLog]
        ring
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  simpa only [← Nat.card_eq_fintype_card] using hcost

end Erdos3.VectorPolynomial

end

end OAI
