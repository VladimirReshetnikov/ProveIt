/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
 Use older set-comprehension and discrete-subgroup names; statements unchanged. -/
import OAI.Compat.Core
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedCanonicalNormalizer

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "coordinates" => allocatedRowIdealCoordinates B U b S rowSets
local notation "reference" => allocatedLongJetReference B U b S rowTypes
local notation "physicalVolume" => (∏ q : (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a))),
  R (Sigma.fst (Subtype.val (Sigma.fst q))) : ℝ)
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

omit [Fintype α] in
theorem allocatedRowIdealCoordinates_measurable : Measurable coordinates := by
  apply Measurable.of_eval
  intro s
  apply Measurable.of_eval
  intro a
  unfold allocatedRowIdealCoordinates realRowsSiteValue
  apply Finset.measurable_sum
  intro t _
  by_cases ha : ¬grid a
  · simpa only [dite_eq_left ha, Function.comp_def] using
      (((measurable_pi_apply ⟨⟨a, ha⟩, t⟩).comp
        (allocatedLongJetRealCoordinates_measurable B U b S (O := rowTypes))).div_const (R a.1)).mul_const
          (if t.val ⊆ s then (1 : ℝ) else 0)
  · simp only [dite_eq_right ha, zero_mul]
    exact measurable_const

theorem allocatedRowIdealCoordinates_rows_bound
    (z : AllocatedLongJetRows B U b S rowTypes) {T : ℝ} (hT : 0 ≤ T)
    (hz : ∀ s a, |coordinates z s a| ≤ T) :
    ‖fun q : (Σ a : {a // ¬grid a}, rowTypes a.val.1) =>
      allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1‖ ≤ (2 : ℝ) ^ Fintype.card α * T := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) hT)).mpr
  intro q
  change |allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1| ≤ _
  rw [← allocatedRowIdealCoordinates_jet B U b S rowSets z q.1 q.2]
  exact (booleanCoefficient_abs_le _ _ (fun s _ => hz s q.1.val)).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ q.2.val)) hT)

noncomputable def allocatedRowIdealEnvelope (r : ℝ≥0) (z : AllocatedLongJetRows B U b S rowTypes) : ℝ :=
  if ∀ s a, |coordinates z s a| ≤ 2 * (r : ℝ) then physicalVolume⁻¹ else 0

theorem allocatedRowIdealEnvelope_measurable (r : ℝ≥0) :
    Measurable (allocatedRowIdealEnvelope B U b S rowSets r) := by
  have hs : MeasurableSet {z : AllocatedLongJetRows B U b S rowTypes |
      ∀ s a, |coordinates z s a| ≤ 2 * (r : ℝ)} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro s
    apply MeasurableSet.iInter
    intro a
    exact measurableSet_le
      (((measurable_pi_apply a).comp ((measurable_pi_apply s).comp
        (allocatedRowIdealCoordinates_measurable B U b S rowSets))).abs) measurable_const
  exact Measurable.ite hs measurable_const measurable_const

theorem allocatedRowIdealEnvelope_nonneg (hR : ∀ j, 0 < R j) (r : ℝ≥0)
    (z : AllocatedLongJetRows B U b S rowTypes) :
    0 ≤ allocatedRowIdealEnvelope B U b S rowSets r z := by
  unfold allocatedRowIdealEnvelope
  split_ifs
  · exact inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le))
  · exact le_rfl

theorem allocatedRowIdealEnvelope_le_box (hR : ∀ j, 0 < R j) (r : ℝ≥0)
    (z : AllocatedLongJetRows B U b S rowTypes) :
    allocatedRowIdealEnvelope B U b S rowSets r z ≤
      (allocatedPhysicalLongJetBox B U b S rowTypes ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ)))).indicator
        (fun _ => physicalVolume⁻¹) z := by
  by_cases hs : ∀ s a, |coordinates z s a| ≤ 2 * (r : ℝ)
  · have hz := allocatedPhysicalLongJetBox_of_normalizedCoordinates B U b S rowTypes hR
      (T := (2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) (by positivity) z
      (allocatedRowIdealCoordinates_rows_bound B U b S rowSets z (by positivity) hs)
    simp only [allocatedRowIdealEnvelope, ite_eq_left hs, Set.indicator_of_mem hz, le_refl]
  · simp only [allocatedRowIdealEnvelope, ite_eq_right hs]
    exact Set.indicator_nonneg
      (fun _ _ => inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le))) z

theorem allocatedRowIdealEnvelope_integrable (hR : ∀ j, 0 < R j) (r : ℝ≥0) :
    Integrable (allocatedRowIdealEnvelope B U b S rowSets r) reference := by
  let T : ℝ := (2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))
  have hg : Integrable ((allocatedPhysicalLongJetBox B U b S rowTypes T).indicator
      (fun _ => physicalVolume⁻¹)) reference :=
    (integrableOn_const (allocatedPhysicalLongJetBox_measure_lt_top B U b S rowTypes T).ne).integrable_indicator
      (allocatedPhysicalLongJetBox_measurable B U b S rowTypes T)
  apply hg.mono' (allocatedRowIdealEnvelope_measurable B U b S rowSets r).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (allocatedRowIdealEnvelope_nonneg B U b S rowSets hR r z)]
  exact allocatedRowIdealEnvelope_le_box B U b S rowSets hR r z

theorem allocatedRowIdealEnvelope_integral_le (hR : ∀ j, 0 < R j)
    (hσ1 : ∀ j, σ j ≤ 1) (r : ℝ≥0) :
    (∫ z, allocatedRowIdealEnvelope B U b S rowSets r z ∂reference) ≤
      (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) * scale := by
  let T : ℝ := (2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))
  have hV : 0 < physicalVolume := Finset.prod_pos (fun q _ => hR q.1.val.1)
  have hg : Integrable ((allocatedPhysicalLongJetBox B U b S rowTypes T).indicator
      (fun _ => physicalVolume⁻¹)) reference :=
    (integrableOn_const (allocatedPhysicalLongJetBox_measure_lt_top B U b S rowTypes T).ne).integrable_indicator
      (allocatedPhysicalLongJetBox_measurable B U b S rowTypes T)
  calc
    _ ≤ ∫ z, (allocatedPhysicalLongJetBox B U b S rowTypes T).indicator
        (fun _ => physicalVolume⁻¹) z ∂reference :=
      integral_mono (allocatedRowIdealEnvelope_integrable B U b S rowSets hR r) hg
        (allocatedRowIdealEnvelope_le_box B U b S rowSets hR r)
    _ = physicalVolume⁻¹ * (reference).real (allocatedPhysicalLongJetBox B U b S rowTypes T) := by
      rw [integral_indicator (allocatedPhysicalLongJetBox_measurable B U b S rowTypes T),
        setIntegral_const, smul_eq_mul]
      ring
    _ ≤ physicalVolume⁻¹ * ((2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) *
        physicalVolume * scale) :=
      mul_le_mul_of_nonneg_left (allocatedPhysicalLongJetBox_measure_bound B U b S rowTypes hR hσ1 (by positivity))
        (inv_nonneg.mpr hV.le)
    _ = _ := by
      dsimp only [T]
      field_simp [hV.ne']

theorem allocatedRowIdealEnvelope_normalized_integral_le (hR : ∀ j, 0 < R j)
    (hσ1 : ∀ j, σ j ≤ 1) (r : ℝ≥0) :
    (∫ z, allocatedRowIdealEnvelope B U b S rowSets r z / scale ∂reference) ≤
      (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) := by
  have hscale : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  rw [integral_div]
  exact (div_le_iff₀ hscale).mpr (allocatedRowIdealEnvelope_integral_le B U b S rowSets hR hσ1 r)

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

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "physicalVolume" => (∏ q : (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a))),
  R (Sigma.fst (Subtype.val (Sigma.fst q))) : ℝ)

variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) *
  (Fintype.card (Finset α) * (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedProductSiteCutoff_row_support
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j)))
    (hne : cutoff (chart z) ≠ 0) :
    ∀ s a, |allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s a| ≤ 2 * (r : ℝ) := by
  intro s a
  have hs := allocatedProductSiteCutoff_sites_quarter B U b S rowSets o hb bW d r hr hR C hC hchart hbudget z hz hne s
  have hsite : allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
      (coveredRowsSiteValue rowSets U (chart z) s) ≠ 0 := by
    intro he
    apply hne
    exact Finset.prod_eq_zero (Finset.mem_univ s) he
  have hraw : allocatedBufferedMixedSiteFactor B U b S r hr (fun _ => 1)
      (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) ≠ 0 := by
    intro he
    apply hsite
    rw [← mixedCoveredRowsSiteValue_chart rowSets U o b hb bW d z s,
      allocatedBufferedSiteChartFactor, restrictedComplexChartDensity_apply _ _ _ _
        (mixedCoveredJetChart_injOn U o b hb bW d
          (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
          (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hs,
      Complex.ofReal_one, one_mul, he]
  rw [allocatedRowIdealCoordinates_mixed_value B U b S rowSets d z s,
    ← allocatedFullMixedSiteValue_projection B U b S]
  have hbnd := bufferedCoordinateProjection_nonzero_box
    (allocatedGridAxis (I := I) U b S.value) r hr (fun _ => (1 : ℂ)) _ hraw a
  change |if grid a then 0 else _| ≤ _
  split_ifs
  · simpa only [abs_zero] using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) r.coe_nonneg)
  · exact hbnd

include hR hC hchart hbudget in
theorem allocatedProductSiteCutoff_le_row_envelope
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))) :
    ‖cutoff (chart z)‖ / physicalVolume ≤
      allocatedRowIdealEnvelope B U b S rowSets r (split z.1).2 := by
  by_cases hzero : cutoff (chart z) = 0
  · simpa only [hzero, norm_zero, zero_div] using
      allocatedRowIdealEnvelope_nonneg B U b S rowSets hR r (split z.1).2
  · have hs := allocatedProductSiteCutoff_row_support B U b S rowSets o hb bW d r hr hR C hC hchart hbudget z hz hzero
    rw [allocatedRowIdealEnvelope, ite_eq_left hs]
    have hV : 0 < physicalVolume := Finset.prod_pos (fun q _ => hR q.1.val.1)
    apply (div_le_iff₀ hV).mpr
    simpa only [inv_mul_cancel₀ hV.ne'] using allocatedProductSiteCutoff_norm B U b S rowSets o hb bW d r hr (chart z)

local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

include hR hC hchart hbudget in
theorem allocatedProductIdealNormalizer_cutoff_le_row_envelope
    {A : ℝ} (hA : 0 ≤ A) (z : MixedCoveredJetSource I rowTypes E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ * A * ‖cutoff (chart z)‖ ≤
      ‖((baseVolume : ℝ) : ℂ)⁻¹‖ * A * allocatedRowIdealEnvelope B U b S rowSets r (split z.1).2 := by
  have hV : 0 < physicalVolume := Finset.prod_pos (fun q _ => hR q.1.val.1)
  have hnorm : ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ =
      ‖((baseVolume : ℝ) : ℂ)⁻¹‖ / physicalVolume := by
    have hvnorm : ‖(physicalVolume : ℂ)‖ = physicalVolume := by
      rw [Complex.norm_real, Real.norm_of_nonneg hV.le]
    simp only [allocatedProductIdealNormalizer, Complex.ofReal_mul, norm_inv, norm_mul,
      hvnorm, mul_inv_rev, div_eq_mul_inv]
    ring
  calc
    _ = (‖((baseVolume : ℝ) : ℂ)⁻¹‖ * A) * (‖cutoff (chart z)‖ / physicalVolume) := by
      rw [hnorm]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (allocatedProductSiteCutoff_le_row_envelope B U b S rowSets o hb bW d r hr hR C hC hchart hbudget z hz)
      (mul_nonneg (norm_nonneg _) hA)

end Erdos3.VectorPolynomial

end

end OAI
