/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Prove the uniform grid-volume comparison by splitting the full product into
grid and non-grid axes, replacing a newer product-injection lemma.
All upstream theorem statements are unchanged. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedProductCutoffEnvelope

namespace OAI

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
theorem allocatedProductSiteCutoff_full_site_support
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j)))
    (hne : cutoff (chart z) ≠ 0) :
    ∀ s a, |allocatedFullMixedSiteValue (R := R) U b
      (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) a| ≤ 2 * (r : ℝ) := by
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
  exact bufferedCoordinateProjection_nonzero_box
    (allocatedGridAxis (I := I) U b S.value) r hr (fun _ => (1 : ℂ)) _ hraw a

include hR hC hchart hbudget in
theorem allocatedProductSiteCutoff_integer_rows
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j)))
    (hne : cutoff (chart z) ≠ 0) (j : Fin m) (i : Fin (n j)) (t : rowTypes j) :
    |((z.1 j).2 i t : ℝ)| ≤
      ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) * (R j * (basisAxisScale (b j) i : ℝ)) := by
  have hbpos : (0 : ℝ) < basisAxisScale (b j) i := Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)
  have hsites (s : Finset α) :
      |(integerBooleanSitesFromRows (rowSets j) ((z.1 j).2 i) s : ℝ)| ≤
        (2 * (r : ℝ)) * (R j * (basisAxisScale (b j) i : ℝ)) := by
    have h := allocatedProductSiteCutoff_full_site_support B U b S rowSets o hb bW d r hr
      hR C hC hchart hbudget z hz hne s ⟨j, .inr i⟩
    change |(((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ℝ) /
      (basisAxisScale (b j) i : ℝ) / R j| ≤ _ at h
    rw [mixedCoveredRowsSiteValue_integer, abs_div, abs_div, abs_of_pos hbpos, abs_of_pos (hR j)] at h
    have h1 := (div_le_iff₀ (hR j)).mp h
    have h2 := (div_le_iff₀ hbpos).mp h1
    nlinarith
  have h := integer_boolean_coefficient_degree_bound
    (integerBooleanSitesFromRows (rowSets j) ((z.1 j).2 i)) t.val (Finset.card_le_univ t.val)
    (by positivity : 0 ≤ 2 * (r : ℝ)) (mul_nonneg (hR j).le hbpos.le) hsites
  rw [integerBooleanSitesFromRows_coefficient_mem] at h
  simpa only [mul_assoc] using h

include hR hC hchart hbudget in
theorem allocatedProductSiteCutoff_grid_natural_bound
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j)))
    (hne : cutoff (chart z) ≠ 0)
    (a : {a // grid a}) (t : rowTypes (allocatedGridIntegerAxis B U b S a).1) :
    |(allocatedGridIntegerValues B U b S rowSets a ((split z.1).1 a) t : ℝ)| ≤
      (((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) *
        (8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
          (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1))) *
        (allocatedGridNaturalScale B U b S a : ℝ) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · have hN : (0 : ℝ) < allocatedPrincipalGridScale (G := G) B U b (R := R) j i :=
      Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
    have hratio := allocatedPrincipalChartRatio_le (G := G) B U b hR j i
    change (basisAxisScale (b j) i : ℝ) / (allocatedPrincipalGridScale (G := G) B U b (R := R) j i : ℝ) ≤
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) / R j at hratio
    have hscale := (div_le_div_iff₀ hN (hR j)).mp hratio
    have hrow := allocatedProductSiteCutoff_integer_rows B U b S rowSets o hb bW d r hr
      hR C hC hchart hbudget z hz hne j i t
    change |((z.1 j).2 i t : ℝ)| ≤ _
    apply hrow.trans
    have hT : 0 ≤ (2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ)) := by positivity
    simpa only [allocatedGridNaturalScale, allocatedGridIntegerAxis, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left hscale hT

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal ENNReal

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

local notation "gridAxes" => {a // grid a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "gridRef" => allocatedFrozenJetReference B U b S rowTypes

noncomputable def allocatedCutoffGridRadius (a : gridAxes) : ℝ :=
  ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) *
    (8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a).1 (ig a).2) : ℝ) + 1))

omit [DecidableEq α] in
theorem allocatedCutoffGridRadius_nonneg (a : gridAxes) :
    0 ≤ allocatedCutoffGridRadius (α := α) B U b S r a := by
  unfold allocatedCutoffGridRadius
  positivity

noncomputable def allocatedCutoffGridRowWindow (a : gridAxes) :
    Finset (CoefficientJetAxisRow rowTypes a.val) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact naturalScaleIntegerWindow (rowSets j)
      (allocatedCutoffGridRadius (α := α) B U b S r ⟨⟨j, .inr i⟩, ha⟩)
      (allocatedPrincipalGridScale (G := G) B U b (R := R) j i)

include hR in
omit [DecidableEq α] in
theorem allocatedCutoffGridRowWindow_card_le (a : gridAxes) :
    ((allocatedCutoffGridRowWindow B U b S rowSets r a).card : ℝ) ≤
      (2 * allocatedCutoffGridRadius (α := α) B U b S r a + 3) ^ (rowSets (ig a).1).card *
        (axisN a : ℝ) ^ (rowSets (ig a).1).card := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · dsimp only [allocatedCutoffGridRowWindow, allocatedGridNaturalScale, allocatedGridIntegerAxis]
    convert naturalScaleIntegerWindow_card_le (rowSets j)
      (allocatedCutoffGridRadius_nonneg (α := α) B U b S r ⟨⟨j, .inr i⟩, ha⟩)
      (allocatedPrincipalGridScale_pos_of_radius (G := G) B U b hR j i) using 1
    · congr 2
    · simp only [Fintype.card_coe]

omit [DecidableEq α] in
theorem allocatedCutoffGridRowWindow_measurable (a : gridAxes) :
    MeasurableSet (↑(allocatedCutoffGridRowWindow B U b S rowSets r a) : Set (CoefficientJetAxisRow rowTypes a.val)) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · change MeasurableSet (↑(naturalScaleIntegerWindow (rowSets j)
        (allocatedCutoffGridRadius (α := α) B U b S r ⟨⟨j, .inr i⟩, ha⟩)
        (allocatedPrincipalGridScale (G := G) B U b (R := R) j i)) : Set (rowTypes j → ℤ))
    exact Finset.measurableSet _

omit [DecidableEq α] in
theorem allocatedCutoffGridRowWindow_measure_lt_top (a : gridAxes) :
    coefficientJetAxisReference rowTypes a.val (↑(allocatedCutoffGridRowWindow B U b S rowSets r a) :
      Set (CoefficientJetAxisRow rowTypes a.val)) < ∞ := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · change Measure.count (↑(naturalScaleIntegerWindow (rowSets j)
        (allocatedCutoffGridRadius (α := α) B U b S r ⟨⟨j, .inr i⟩, ha⟩)
        (allocatedPrincipalGridScale (G := G) B U b (R := R) j i)) : Set (rowTypes j → ℤ)) < ∞
    rw [Measure.count_apply_finset]
    simp

noncomputable def allocatedCutoffGridRegion : Set (AllocatedFrozenJetRows B U b S rowTypes) :=
  Set.univ.pi (fun a => (↑(allocatedCutoffGridRowWindow B U b S rowSets r a) : Set (CoefficientJetAxisRow rowTypes a.val)))

noncomputable def allocatedCutoffGridVolumeCap : ℝ :=
  ∏ a : gridAxes, (2 * allocatedCutoffGridRadius (α := α) B U b S r a + 3) ^ (rowSets (ig a).1).card

omit [DecidableEq α] in
theorem allocatedCutoffGridRegion_measurable :
    MeasurableSet (allocatedCutoffGridRegion B U b S rowSets r) :=
  MeasurableSet.univ_pi (allocatedCutoffGridRowWindow_measurable B U b S rowSets r)

omit [DecidableEq α] in
theorem allocatedCutoffGridRegion_measure_lt_top :
    gridRef (allocatedCutoffGridRegion B U b S rowSets r) < ∞ := by
  rw [allocatedFrozenJetReference, allocatedCutoffGridRegion, Measure.pi_pi]
  exact ENNReal.prod_lt_top (fun a _ => allocatedCutoffGridRowWindow_measure_lt_top B U b S rowSets r a)

include hR in
omit [DecidableEq α] in
theorem allocatedCutoffGridRegion_measure_le :
    (gridRef).real (allocatedCutoffGridRegion B U b S rowSets r) ≤
      allocatedCutoffGridVolumeCap B U b S rowSets r * allocatedFullGridNaturalVolume B U b S rowSets := by
  have hrow (a : gridAxes) : (coefficientJetAxisReference rowTypes a.val).real
      (↑(allocatedCutoffGridRowWindow B U b S rowSets r a) : Set (CoefficientJetAxisRow rowTypes a.val)) ≤
        (2 * allocatedCutoffGridRadius (α := α) B U b S r a + 3) ^ (rowSets (ig a).1).card *
          (axisN a : ℝ) ^ (rowSets (ig a).1).card := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · change (Measure.count : Measure (rowTypes j → ℤ)).real
        (↑(naturalScaleIntegerWindow (rowSets j)
        (allocatedCutoffGridRadius (α := α) B U b S r ⟨⟨j, .inr i⟩, ha⟩)
        (allocatedPrincipalGridScale (G := G) B U b (R := R) j i)) : Set (rowTypes j → ℤ)) ≤ _
      rw [measureReal_def, Measure.count_apply_finset, ENNReal.toReal_natCast]
      exact allocatedCutoffGridRowWindow_card_le B U b S rowSets r hR ⟨⟨j, .inr i⟩, ha⟩
  calc
    _ = ∏ a : gridAxes, (coefficientJetAxisReference rowTypes a.val).real
        (↑(allocatedCutoffGridRowWindow B U b S rowSets r a) : Set (CoefficientJetAxisRow rowTypes a.val)) := by
      simp only [measureReal_def, allocatedFrozenJetReference, allocatedCutoffGridRegion,
        Measure.pi_pi, ENNReal.toReal_prod]
    _ ≤ ∏ a : gridAxes, ((2 * allocatedCutoffGridRadius (α := α) B U b S r a + 3) ^ (rowSets (ig a).1).card *
          (axisN a : ℝ) ^ (rowSets (ig a).1).card) :=
      Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg) (fun a _ => hrow a)
    _ = _ := by rw [Finset.prod_mul_distrib]; rfl

omit [DecidableEq α] in
theorem allocatedCutoffGridRegion_mem_of_bound
    (z : AllocatedFrozenJetRows B U b S rowTypes)
    (hz : ∀ a t, |(allocatedGridIntegerValues B U b S rowSets a (z a) t : ℝ)| ≤
      allocatedCutoffGridRadius (α := α) B U b S r a * (axisN a : ℝ)) :
    z ∈ allocatedCutoffGridRegion B U b S rowSets r := by
  apply Set.mem_univ_pi.mpr
  intro a
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact mem_naturalScaleIntegerWindow_of_bound _ _ _ (hz ⟨⟨j, .inr i⟩, ha⟩)

include hR hC hchart hbudget in
theorem allocatedProductSiteCutoff_mem_gridRegion
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j)))
    (hne : cutoff (chart z) ≠ 0) :
    (split z.1).1 ∈ allocatedCutoffGridRegion B U b S rowSets r :=
  allocatedCutoffGridRegion_mem_of_bound B U b S rowSets r (split z.1).1
    (allocatedProductSiteCutoff_grid_natural_bound B U b S rowSets o hb bW d r hr hR C hC hchart hbudget z hz hne)

noncomputable def allocatedCutoffGridEnvelope (z : AllocatedFrozenJetRows B U b S rowTypes) : ℝ :=
  (allocatedCutoffGridRegion B U b S rowSets r).indicator
    (fun _ => (allocatedFullGridNaturalVolume B U b S rowSets)⁻¹) z

include hR in
omit [DecidableEq α] in
theorem allocatedCutoffGridEnvelope_nonneg (z : AllocatedFrozenJetRows B U b S rowTypes) :
    0 ≤ allocatedCutoffGridEnvelope B U b S rowSets r z := by
  apply Set.indicator_nonneg
  intro _ _
  exact inv_nonneg.mpr (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le

omit [DecidableEq α] in
theorem allocatedCutoffGridEnvelope_measurable :
    Measurable (allocatedCutoffGridEnvelope B U b S rowSets r) :=
  measurable_const.indicator (allocatedCutoffGridRegion_measurable B U b S rowSets r)

omit [DecidableEq α] in
theorem allocatedCutoffGridEnvelope_integrable :
    Integrable (allocatedCutoffGridEnvelope B U b S rowSets r) gridRef :=
  (integrableOn_const (allocatedCutoffGridRegion_measure_lt_top B U b S rowSets r).ne).integrable_indicator
    (allocatedCutoffGridRegion_measurable B U b S rowSets r)

include hR in
omit [DecidableEq α] in
theorem allocatedCutoffGridEnvelope_integral_le :
    (∫ z, allocatedCutoffGridEnvelope B U b S rowSets r z ∂gridRef) ≤
      allocatedCutoffGridVolumeCap B U b S rowSets r := by
  have hN := allocatedFullGridNaturalVolume_pos B U b hR S rowSets
  unfold allocatedCutoffGridEnvelope
  rw [integral_indicator (allocatedCutoffGridRegion_measurable B U b S rowSets r),
    setIntegral_const, smul_eq_mul]
  calc
    _ ≤ (allocatedCutoffGridVolumeCap B U b S rowSets r * allocatedFullGridNaturalVolume B U b S rowSets) *
        (allocatedFullGridNaturalVolume B U b S rowSets)⁻¹ :=
      mul_le_mul_of_nonneg_right (allocatedCutoffGridRegion_measure_le B U b S rowSets r hR) (inv_nonneg.mpr hN.le)
    _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hN.ne', mul_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal ENNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α]
variable (rowSets : Fin m → Finset (Finset α))
variable (r : ℝ≥0)

noncomputable def allocatedUniformGridVolumeCap : ℝ :=
  ∏ a : LayerSamplerAxis I n,
    (2 * (((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) *
      (8 * ((Fintype.card (B a) : ℝ) + 1))) + 3) ^ (rowSets a.1).card

theorem allocatedUniformGridVolumeCap_one_le :
    1 ≤ allocatedUniformGridVolumeCap B rowSets r := by
  unfold allocatedUniformGridVolumeCap
  apply Finset.one_le_prod₀
  intro a _
  apply one_le_pow₀
  have h : 0 ≤ (((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) *
      (8 * ((Fintype.card (B a) : ℝ) + 1))) := by positivity
  linarith

theorem allocatedCutoffGridVolumeCap_le_uniform :
    allocatedCutoffGridVolumeCap B U b S rowSets r ≤ allocatedUniformGridVolumeCap B rowSets r := by
  let F (a : LayerSamplerAxis I n) : ℝ :=
    (2 * (((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) *
      (8 * ((Fintype.card (B a) : ℝ) + 1))) + 3) ^ (rowSets a.1).card
  have hF (a : LayerSamplerAxis I n) : 1 ≤ F a := by
    apply one_le_pow₀
    have h : 0 ≤ (((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) *
        (8 * ((Fintype.card (B a) : ℝ) + 1))) := by positivity
    linarith
  have he : allocatedCutoffGridVolumeCap B U b S rowSets r =
      ∏ a : {a // allocatedGridAxis (I := I) U b S.value a}, F a.val := by
    apply Finset.prod_congr rfl
    intro a _
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · dsimp only [allocatedCutoffGridRadius, allocatedGridIntegerAxis, F]
      rw [layerIntegerPrincipalSlots_card]
  change allocatedCutoffGridVolumeCap B U b S rowSets r ≤ ∏ a, F a
  rw [he, ← Fintype.prod_subtype_mul_prod_subtype
    (allocatedGridAxis (I := I) U b S.value) F]
  exact le_mul_of_one_le_right
    (Finset.prod_nonneg (fun a _ => zero_le_one.trans (hF a.val)))
    (Finset.one_le_prod (fun a _ => hF a.val))

end Erdos3.VectorPolynomial

end

end OAI
