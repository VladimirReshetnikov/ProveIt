import OAI.Combinatorics.Progressions.Sampling.AllocatedUniformGridVolumeCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

theorem mixedCoveredReference_product_mass_data
    {m : ℕ} {I O E : Fin m → Type*} {n : Fin m → ℕ}
    [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (E j)]
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] (d : ℕ) [NeZero d]
    (g : (∀ a : {a // P a}, CoefficientJetAxisRow O a.val) → ℝ)
    (f : (∀ a : {a // ¬P a}, CoefficientJetAxisRow O a.val) → ℝ)
    (hg : Integrable g (Measure.pi (fun a : {a // P a} => coefficientJetAxisReference O a.val)))
    (hf : Integrable f (Measure.pi (fun a : {a // ¬P a} => coefficientJetAxisReference O a.val))) :
    Integrable (fun z : MixedCoveredJetSource I O E n d =>
      g (coefficientJetAxisSplit O I n P z.1).1 * f (coefficientJetAxisSplit O I n P z.1).2)
        (mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d) ∧
      (∫ z : MixedCoveredJetSource I O E n d,
        g (coefficientJetAxisSplit O I n P z.1).1 * f (coefficientJetAxisSplit O I n P z.1).2
          ∂mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d) =
        (∫ z, g z ∂Measure.pi (fun a : {a // P a} => coefficientJetAxisReference O a.val)) *
          ∫ z, f z ∂Measure.pi (fun a : {a // ¬P a} => coefficientJetAxisReference O a.val) := by
  let μd := (PMF.uniformOfFintype (∀ j, O j → E j → ZMod d)).toMeasure
  let μ := Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
  let split := coefficientJetAxisSplit O I n P
  let F := fun z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ) =>
    g (split z).1 * f (split z).2
  have hs := coefficientJetAxisSplit_measurePreserving O I n P
  have hF : Integrable F μ := (hs.integrable_comp_emb split.measurableEmbedding).mpr (hg.mul_prod hf)
  have hmass : μd.real Set.univ = 1 := by simp
  constructor
  · change Integrable (fun z : MixedCoveredJetSource I O E n d => F z.1) (μ.prod μd)
    exact hF.comp_fst μd
  · change (∫ z, F z.1 ∂μ.prod μd) = _
    rw [integral_fun_fst, hmass, one_smul]
    change (∫ z, (fun w : (∀ a : {a // P a}, CoefficientJetAxisRow O a.val) ×
      (∀ a : {a // ¬P a}, CoefficientJetAxisRow O a.val) => g w.1 * f w.2) (split z) ∂μ) = _
    dsimp only [split, μ]
    exact (hs.integral_comp split.measurableEmbedding
      (fun w : (∀ a : {a // P a}, CoefficientJetAxisRow O a.val) ×
        (∀ a : {a // ¬P a}, CoefficientJetAxisRow O a.val) => g w.1 * f w.2)).trans
      (integral_prod_mul g f)

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

local notation "gridRef" => allocatedFrozenJetReference B U b S rowTypes
local notation "longRef" => allocatedLongJetReference B U b S rowTypes
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := rowTypes) (E := E) (n := n) d
local notation "gridE" => allocatedCutoffGridEnvelope B U b S rowSets r
local notation "longE" => allocatedRowIdealEnvelope B U b S rowSets r
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

noncomputable def allocatedCutoffRawEnvelope (z : MixedCoveredJetSource I rowTypes E n d) : ℝ :=
  gridE (split z.1).1 * (longE (split z.1).2 / scale)

omit [∀ j, Fintype (E j)] [NeZero d] in
theorem allocatedCutoffRawEnvelope_measurable :
    Measurable (allocatedCutoffRawEnvelope (E := E) B U b S rowSets d r) := by
  have hs : Measurable (fun z : MixedCoveredJetSource I rowTypes E n d => split z.1) :=
    (split).measurable.comp measurable_fst
  exact ((allocatedCutoffGridEnvelope_measurable B U b S rowSets r).comp (measurable_fst.comp hs)).mul
    (((allocatedRowIdealEnvelope_measurable B U b S rowSets r).comp (measurable_snd.comp hs)).div_const _)

include hR in
omit [∀ j, Fintype (E j)] [NeZero d] in
theorem allocatedCutoffRawEnvelope_nonneg (z : MixedCoveredJetSource I rowTypes E n d) :
    0 ≤ allocatedCutoffRawEnvelope B U b S rowSets d r z := by
  exact mul_nonneg (allocatedCutoffGridEnvelope_nonneg B U b S rowSets r hR _)
    (div_nonneg (allocatedRowIdealEnvelope_nonneg B U b S rowSets hR r _)
      (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le)))

include hR in
theorem allocatedCutoffRawEnvelope_mass_data :
    Integrable (allocatedCutoffRawEnvelope (E := E) B U b S rowSets d r) raw ∧
      (∫ z, allocatedCutoffRawEnvelope (E := E) B U b S rowSets d r z ∂raw) =
        (∫ z, gridE z ∂gridRef) * ∫ z, longE z / scale ∂longRef := by
  exact mixedCoveredReference_product_mass_data (O := rowTypes) (E := E) grid d
    gridE (fun z => longE z / scale) (allocatedCutoffGridEnvelope_integrable B U b S rowSets r)
    ((allocatedRowIdealEnvelope_integrable B U b S rowSets hR r).div_const _)

include hR in
theorem allocatedCutoffRawEnvelope_integral_le (hσ1 : ∀ j, σ j ≤ 1) :
    (∫ z, allocatedCutoffRawEnvelope (E := E) B U b S rowSets d r z ∂raw) ≤
      allocatedCutoffGridVolumeCap B U b S rowSets r *
        (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) := by
  rw [(allocatedCutoffRawEnvelope_mass_data (E := E) B U b S rowSets d r hR).2]
  have hg := allocatedCutoffGridEnvelope_integral_le B U b S rowSets r hR
  have hl := allocatedRowIdealEnvelope_normalized_integral_le B U b S rowSets hR hσ1 r
  apply mul_le_mul hg hl
  · apply integral_nonneg
    intro z
    exact div_nonneg (allocatedRowIdealEnvelope_nonneg B U b S rowSets hR r z)
      (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))
  · exact (integral_nonneg (allocatedCutoffGridEnvelope_nonneg B U b S rowSets r hR)).trans hg

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

local notation "gridRef" => allocatedFrozenJetReference B U b S rowTypes
local notation "longRef" => allocatedLongJetReference B U b S rowTypes
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := rowTypes) (E := E) (n := n) d
local notation "gridE" => allocatedCutoffGridEnvelope B U b S rowSets r
local notation "longE" => allocatedRowIdealEnvelope B U b S rowSets r
local notation "scale" => (∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "rawE" => allocatedCutoffRawEnvelope (E := E) B U b S rowSets d r
local notation "coverScale" => coveredJetArrayScale (O := rowTypes) U

noncomputable def allocatedCutoffCoveredEnvelope : EuclideanJetLayers U rowTypes → ℝ :=
  restrictedChartDensity chart region 1 (fun z => rawE z / coverScale)

theorem allocatedCutoffCoveredEnvelope_measurable :
    Measurable (allocatedCutoffCoveredEnvelope B U b S rowSets o hb bW d r) :=
  mixedCoveredJet_restrictedDensity_measurable U o b hb bW d _
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) _
    ((allocatedCutoffRawEnvelope_measurable (E := E) B U b S rowSets d r).div_const _)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

include hR in
theorem allocatedCutoffCoveredEnvelope_nonneg (y : EuclideanJetLayers U rowTypes) :
    0 ≤ allocatedCutoffCoveredEnvelope B U b S rowSets o hb bW d r y := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedCutoffCoveredEnvelope, restrictedChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d _
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz, one_mul]
    exact div_nonneg (allocatedCutoffRawEnvelope_nonneg B U b S rowSets d r hR z) (coveredJetArrayScale_pos U).le
  · rw [allocatedCutoffCoveredEnvelope, restrictedChartDensity_zero _ _ _ _ hy]

include hR hC hchart hbudget in
theorem allocatedProductIdealNormalizer_cutoff_le_covered_envelope
    (y : EuclideanJetLayers U rowTypes) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ * ‖cutoff y‖ ≤
      allocatedCutoffCoveredEnvelope B U b S rowSets o hb bW d r y := by
  by_cases hzero : cutoff y = 0
  · simpa only [hzero, norm_zero, mul_zero] using
      allocatedCutoffCoveredEnvelope_nonneg B U b S rowSets o hb bW d r hR y
  have hrow : ∀ j, Fintype.card (Finset α) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j))) ≤ 1 / 4 := by
    intro j
    have hn : 0 ≤ (Fintype.card (Finset α) : ℝ) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j))) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC j)
        (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le)))
    nlinarith [hbudget j, Nat.cast_nonneg (α := ℝ) (rowSets j).card]
  obtain ⟨z, hz, rfl⟩ := allocatedProductSiteCutoff_mem_chart B U b S rowSets o hb bW d r hr
    hR C hC hchart hrow y hzero
  have hg := allocatedProductSiteCutoff_mem_gridRegion B U b S rowSets o hb bW d r hr
    hR C hC hchart hbudget z hz hzero
  have h := allocatedProductIdealNormalizer_cutoff_le_row_envelope B U b S rowSets o hb bW d r hr
    hR C hC hchart hbudget (A := 1) zero_le_one z hz
  simp only [mul_one] at h
  apply h.trans_eq
  rw [allocatedCutoffCoveredEnvelope, restrictedChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o b hb bW d _
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz, one_mul,
    allocatedCutoffRawEnvelope, allocatedCutoffGridEnvelope, Set.indicator_of_mem hg]
  have hN := allocatedFullGridNaturalVolume_pos B U b hR S rowSets
  have hS : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have hcov : 0 < coverScale := coveredJetArrayScale_pos U
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (mul_pos (mul_pos hN hcov) hS).le]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : rowTypes j => ν j))

include hR in
theorem allocatedCutoffCoveredEnvelope_integrable :
    Integrable (allocatedCutoffCoveredEnvelope B U b S rowSets o hb bW d r) haar :=
  mixedCoveredJet_normalized_integrable U o b hb bW d ν _
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) rawE
    (allocatedCutoffRawEnvelope_measurable (E := E) B U b S rowSets d r)
    (allocatedCutoffRawEnvelope_mass_data (E := E) B U b S rowSets d r hR).1

include hR in
theorem allocatedCutoffCoveredEnvelope_integral_abs_le (hσ1 : ∀ j, σ j ≤ 1) :
    (∫ y, |allocatedCutoffCoveredEnvelope B U b S rowSets o hb bW d r y| ∂haar) ≤
      allocatedCutoffGridVolumeCap B U b S rowSets r *
        (2 * ((2 : ℝ) ^ Fintype.card α * (2 * (r : ℝ))) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) := by
  have h := mixedCoveredJet_normalized_integral_abs_le U o b hb bW d ν _
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).isClosed.measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) rawE
    (allocatedCutoffRawEnvelope_measurable (E := E) B U b S rowSets d r)
    (allocatedCutoffRawEnvelope_mass_data (E := E) B U b S rowSets d r hR).1
  have habs : (fun z => |rawE z|) = rawE := funext (fun z =>
    abs_of_nonneg (allocatedCutoffRawEnvelope_nonneg B U b S rowSets d r hR z))
  rw [habs] at h
  exact h.trans (allocatedCutoffRawEnvelope_integral_le (E := E) B U b S rowSets d r hR hσ1)

end Erdos3.VectorPolynomial

end

end OAI
