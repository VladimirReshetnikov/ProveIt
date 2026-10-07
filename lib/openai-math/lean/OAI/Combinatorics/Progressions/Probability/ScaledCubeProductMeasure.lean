import Mathlib.MeasureTheory.Integral.Pi
import OAI.Combinatorics.Progressions.Estimates.ScalarCubeFaceSlab

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def scalarCubeProductDomain (ι α : Type*) [Fintype ι] [Fintype α] [DecidableEq α] :
    Set (ι → Option α → ℝ) := Set.univ.pi (fun _ => scalarCubeDomain α)

noncomputable def scalarCubeProductMeasure (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] : Measure (ι → Option α → ℝ) :=
  Measure.pi (fun _ : ι => scalarCubeMeasure α)

instance scalarCubeProductMeasure_probability (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] : IsProbabilityMeasure (scalarCubeProductMeasure ι α) := by
  unfold scalarCubeProductMeasure
  infer_instance

theorem scalarCubeProductMeasure_eq_closed (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] :
    scalarCubeProductMeasure ι α = Measure.pi (fun _ : ι => closedScalarCubeMeasure α) := by
  simp only [closedScalarCubeMeasure_eq, scalarCubeProductMeasure]

theorem scalarCubeProductMeasure_eq_smul_restrict (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] :
    scalarCubeProductMeasure ι α =
      (volume (scalarCubeDomain α))⁻¹ ^ Fintype.card ι •
        volume.restrict (scalarCubeProductDomain ι α) := by
  unfold scalarCubeProductMeasure
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  change _ * volume (Set.univ.pi s ∩ Set.univ.pi (fun _ : ι => scalarCubeDomain α)) = _
  rw [← Set.pi_inter_distrib, volume_pi_pi]
  simp only [scalarCubeMeasure, Measure.smul_apply, Measure.restrict_apply (hs _),
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem scalarCubeProductMeasure_integral {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (f : (ι → Option α → ℝ) → ℝ) :
    (∫ x, f x ∂scalarCubeProductMeasure ι α) =
      scalarCubeDomainDensity α ^ Fintype.card ι *
        ∫ x in scalarCubeProductDomain ι α, f x := by
  rw [scalarCubeProductMeasure_eq_smul_restrict, integral_smul_measure,
    ENNReal.toReal_pow, ENNReal.toReal_inv, smul_eq_mul]
  rfl

theorem scalarCubeProductMeasure_ae_domain (ι α : Type*) [Fintype ι] [Fintype α]
    [DecidableEq α] :
    ∀ᵐ x ∂scalarCubeProductMeasure ι α, x ∈ scalarCubeProductDomain ι α := by
  change ∀ᵐ x ∂Measure.pi (fun _ : ι => scalarCubeMeasure α),
    x ∈ Set.univ.pi (fun _ => scalarCubeDomain α)
  have h : ∀ i : ι, ∀ᵐ x ∂Measure.pi (fun _ : ι => scalarCubeMeasure α),
      x i ∈ scalarCubeDomain α := fun _ =>
    Measure.tendsto_eval_ae_ae.eventually (scalarCubeMeasure_ae_domain α)
  filter_upwards [ae_all_iff.mpr h] with x hx
  exact fun i _ => hx i

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable (ι : Type*) [Fintype ι]

theorem unitBoxMeasure_eq_pi :
    unitBoxMeasure ι = Measure.pi (fun _ : ι => unitScalarMeasure) := by
  change (Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict
    (Set.univ.pi (fun _ => Set.Ioc (0 : ℝ) 1)) = _
  exact Measure.restrict_pi_pi _ _

theorem scalarOneCube_product_endpoints :
    (scalarCubeProductMeasure ι (Fin 1)).map
      (fun a => ((fun i => a i none), (fun i => a i none + a i (some 0)))) =
      (unitBoxMeasure ι).prod (unitBoxMeasure ι) := by
  have hscalar : MeasurePreserving oneCubeEndpointEquiv (scalarCubeMeasure (Fin 1))
      (unitScalarMeasure.prod unitScalarMeasure) :=
    ⟨oneCubeEndpointEquiv.measurable, scalarCubeMeasure_one_endpoints⟩
  have hp := measurePreserving_pi (fun _ : ι => scalarCubeMeasure (Fin 1))
    (fun _ : ι => unitScalarMeasure.prod unitScalarMeasure) (fun _ => hscalar)
  have hsplit := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => unitScalarMeasure) (fun _ => unitScalarMeasure)
  have h := (hsplit.comp hp).map_eq
  rw [← unitBoxMeasure_eq_pi ι] at h
  exact h

theorem scalarOneCube_product_image {Y : Type*} [MeasurableSpace Y]
    (F : (ι → ℝ) → Y) (hF : Measurable F) :
    (scalarCubeProductMeasure ι (Fin 1)).map
      (fun a => (F (fun i => a i none), F (fun i => a i none + a i (some 0)))) =
      ((unitBoxMeasure ι).map F).prod ((unitBoxMeasure ι).map F) := by
  have hEnd : Measurable (fun a : ι → Option (Fin 1) → ℝ =>
      ((fun i => a i none), (fun i => a i none + a i (some 0)))) := by fun_prop
  rw [Measure.map_prod_map _ _ hF hF, ← scalarOneCube_product_endpoints ι,
    Measure.map_map (hF.prodMap hF) hEnd]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def scaledScalarCubeMeasure (α : Type*) [Fintype α] [DecidableEq α]
    (T : ℝ) : Measure (Option α → ℝ) :=
  (volume (scaledScalarCubeDomain α T))⁻¹ • volume.restrict (scaledScalarCubeDomain α T)

theorem scaledScalarCubeMeasure_eq_map {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) :
    scaledScalarCubeMeasure α T = (scalarCubeMeasure α).map (T • ·) := by
  let e := (Homeomorph.smulOfNeZero (α := Option α → ℝ) T hT.ne').toMeasurableEquiv
  let c := ENNReal.ofReal |(T ^ Module.finrank ℝ (Option α → ℝ))⁻¹|
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr
    (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hT.ne')))).ne'
  have he : (volume : Measure (Option α → ℝ)).map e = c • volume :=
    Measure.map_addHaar_smul volume hT.ne'
  have h := normalizedRestriction_map_equiv e volume volume hc ENNReal.ofReal_ne_top he
    (scalarCubeDomain α)
  change (scalarCubeMeasure α).map (T • ·) =
    (volume ((T • ·) '' scalarCubeDomain α))⁻¹ •
      volume.restrict ((T • ·) '' scalarCubeDomain α) at h
  rw [← scaledScalarCubeDomain_eq_image hT] at h
  exact h.symm

theorem scaledScalarCubeMeasure_probability {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) : IsProbabilityMeasure (scaledScalarCubeMeasure α T) := by
  rw [scaledScalarCubeMeasure_eq_map hT]
  infer_instance

theorem scaledScalarCubeMeasure_normalize {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) :
    (scaledScalarCubeMeasure α T).map (T⁻¹ • ·) = scalarCubeMeasure α := by
  rw [scaledScalarCubeMeasure_eq_map hT,
    Measure.map_map (measurable_const_smul T⁻¹) (measurable_const_smul T)]
  have he : (fun x : Option α → ℝ => T⁻¹ • T • x) = id := by
    funext x
    exact inv_smul_smul₀ hT.ne' x
  rw [show (T⁻¹ • ·) ∘ (T • ·) = (fun x : Option α → ℝ => T⁻¹ • T • x) from rfl,
    he, Measure.map_id]

theorem scaledScalarCubeMeasure_integral {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) (f : (Option α → ℝ) → ℝ) :
    (∫ x, f x ∂scaledScalarCubeMeasure α T) = ∫ x, f (T • x) ∂scalarCubeMeasure α := by
  rw [scaledScalarCubeMeasure_eq_map hT]
  exact (Homeomorph.smulOfNeZero (α := Option α → ℝ) T hT.ne').toMeasurableEquiv.measurableEmbedding.integral_map f

theorem scaledScalarCubeMeasure_ae_domain {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ x ∂scaledScalarCubeMeasure α T, x ∈ scaledScalarCubeDomain α T := by
  rw [scaledScalarCubeMeasure_eq_map hT]
  apply (Homeomorph.smulOfNeZero (α := Option α → ℝ) T hT.ne').toMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [scalarCubeMeasure_ae_domain α] with x hx
  exact (scaledScalarCubeDomain_smul_iff hT x).mpr hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeDomain_empty :
    scalarCubeDomain Empty =
      (fun x : Option Empty → ℝ => x none) ⁻¹' Set.Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    simpa only [Set.mem_preimage, scalarCubeValue_empty] using hx ∅
  · intro hx t
    have ht : t = ∅ := Subsingleton.elim _ _
    simpa only [ht, scalarCubeValue_empty, Set.mem_preimage] using hx

theorem scalarCubeDomain_empty_volume : volume (scalarCubeDomain Empty) = 1 := by
  have hm : MeasurePreserving (fun x : Option Empty → ℝ => x none) volume volume :=
    volume_preserving_funUnique (Option Empty) ℝ
  rw [scalarCubeDomain_empty, hm.measure_preimage measurableSet_Ioo.nullMeasurableSet]
  simp

theorem scalarCubeMeasure_empty_map :
    (scalarCubeMeasure Empty).map (fun x => x none) = unitScalarMeasure := by
  have hm : MeasurePreserving (fun x : Option Empty → ℝ => x none) volume volume :=
    volume_preserving_funUnique (Option Empty) ℝ
  rw [scalarCubeMeasure, scalarCubeDomain_empty_volume, inv_one, one_smul,
    scalarCubeDomain_empty, (hm.restrict_preimage measurableSet_Ioo).map_eq]
  exact restrict_Ioo_eq_restrict_Ioc

theorem scalarCubeProductMeasure_empty_map (J : Type*) [Fintype J] :
    (scalarCubeProductMeasure J Empty).map (fun x j => x j none) = unitBoxMeasure J := by
  have hm : MeasurePreserving (fun x : Option Empty → ℝ => x none)
      (scalarCubeMeasure Empty) unitScalarMeasure :=
    ⟨measurable_pi_apply none, scalarCubeMeasure_empty_map⟩
  have hp := (measurePreserving_pi (fun _ : J => scalarCubeMeasure Empty)
    (fun _ : J => unitScalarMeasure) (fun _ => hm)).map_eq
  simpa only [scalarCubeProductMeasure, unitBoxMeasure_eq_pi] using hp

theorem scalarCubeProductMeasure_empty_integral (J : Type*) [Fintype J]
    (φ : (J → ℝ) → ℝ) (hφ : Measurable φ) :
    (∫ x, φ (fun j => x j none) ∂scalarCubeProductMeasure J Empty) =
      ∫ y, φ y ∂unitBoxMeasure J := by
  have hm : Measurable (fun x : J → Option Empty → ℝ => fun j => x j none) := by fun_prop
  rw [← scalarCubeProductMeasure_empty_map J]
  exact (integral_map hm.aemeasurable hφ.aestronglyMeasurable).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

def scaledClosedCubeDomain (α : Type*) [Fintype α] [DecidableEq α] (T : ℝ) :
    Set (Option α → ℝ) :=
  {a | ∀ vertex : Finset α, scalarCubeValue a vertex ∈ Set.Icc (0 : ℝ) T}

theorem scaledClosedCubeDomain_smul_iff {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) (a : Option α → ℝ) :
    T • a ∈ scaledClosedCubeDomain α T ↔ a ∈ closedScalarCubeDomain α := by
  change (∀ vertex, 0 ≤ scalarCubeValue (T • a) vertex ∧ scalarCubeValue (T • a) vertex ≤ T) ↔ _
  simp only [scalarCubeValue_smul, mul_nonneg_iff_of_pos_left hT,
    mul_le_iff_le_one_right hT]
  rfl

theorem scaledClosedCubeDomain_eq_image {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) :
    scaledClosedCubeDomain α T = (T • ·) '' closedScalarCubeDomain α := by
  ext a
  constructor
  · intro ha
    refine ⟨T⁻¹ • a, ?_, smul_inv_smul₀ hT.ne' a⟩
    apply (scaledClosedCubeDomain_smul_iff hT _).mp
    simpa only [smul_inv_smul₀ hT.ne'] using ha
  · rintro ⟨a, ha, rfl⟩
    exact (scaledClosedCubeDomain_smul_iff hT a).mpr ha

theorem scaledScalarCubeMeasure_eq_closed {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℝ} (hT : 0 < T) :
    scaledScalarCubeMeasure α T =
      (volume (scaledClosedCubeDomain α T))⁻¹ • volume.restrict (scaledClosedCubeDomain α T) := by
  let e := (Homeomorph.smulOfNeZero (α := Option α → ℝ) T hT.ne').toMeasurableEquiv
  let c := ENNReal.ofReal |(T ^ Module.finrank ℝ (Option α → ℝ))⁻¹|
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr
    (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hT.ne')))).ne'
  have he : (volume : Measure (Option α → ℝ)).map e = c • volume :=
    Measure.map_addHaar_smul volume hT.ne'
  have h := normalizedRestriction_map_equiv e volume volume hc ENNReal.ofReal_ne_top he
    (closedScalarCubeDomain α)
  change (closedScalarCubeMeasure α).map (T • ·) =
    (volume ((T • ·) '' closedScalarCubeDomain α))⁻¹ •
      volume.restrict ((T • ·) '' closedScalarCubeDomain α) at h
  rw [closedScalarCubeMeasure_eq, ← scaledClosedCubeDomain_eq_image hT,
    ← scaledScalarCubeMeasure_eq_map hT] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def scaledCubeProductMeasure {I : Type*} [Fintype I]
    (α : Type*) [Fintype α] [DecidableEq α] (T : I → ℝ) :
    Measure (I → Option α → ℝ) :=
  Measure.pi (fun i => scaledScalarCubeMeasure α (T i))

theorem scaledCubeProductMeasure_eq_map {I α : Type*} [Fintype I] [Fintype α]
    [DecidableEq α] (T : I → ℝ) (hT : ∀ i, 0 < T i) :
    scaledCubeProductMeasure α T =
      (scalarCubeProductMeasure I α).map (fun x i => T i • x i) := by
  let : ∀ i, IsProbabilityMeasure ((scalarCubeMeasure α).map (T i • ·)) :=
    fun _ => inferInstance
  rw [scalarCubeProductMeasure, Measure.pi_map_pi
    (fun i => (measurable_const_smul (T i)).aemeasurable)]
  unfold scaledCubeProductMeasure
  congr 1
  funext i
  exact scaledScalarCubeMeasure_eq_map (hT i)

theorem scaledCubeProductMeasure_probability {I α : Type*} [Fintype I] [Fintype α]
    [DecidableEq α] (T : I → ℝ) (hT : ∀ i, 0 < T i) :
    IsProbabilityMeasure (scaledCubeProductMeasure α T) := by
  let : ∀ i, IsProbabilityMeasure (scaledScalarCubeMeasure α (T i)) :=
    fun i => scaledScalarCubeMeasure_probability (hT i)
  unfold scaledCubeProductMeasure
  infer_instance

theorem scaledCubeProductMeasure_eq_smul_restrict {I α : Type*} [Fintype I] [Fintype α]
    [DecidableEq α] (T : I → ℝ) (hT : ∀ i, 0 < T i) :
    scaledCubeProductMeasure α T =
      (∏ i, (volume (scaledScalarCubeDomain α (T i)))⁻¹) •
        volume.restrict (Set.univ.pi (fun i => scaledScalarCubeDomain α (T i))) := by
  let : ∀ i, IsProbabilityMeasure (scaledScalarCubeMeasure α (T i)) :=
    fun i => scaledScalarCubeMeasure_probability (hT i)
  unfold scaledCubeProductMeasure
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs)]
  rw [← Set.pi_inter_distrib, volume_pi_pi]
  simp only [scaledScalarCubeMeasure, Measure.smul_apply, Measure.restrict_apply (hs _),
    smul_eq_mul, Finset.prod_mul_distrib]

end Erdos3

end

end OAI
