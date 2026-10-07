/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements unchanged. Use Set.preimage_setOf_eq for predicate preimages. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Dynamics.ScalarCubeBoundaryLogBudget
import OAI.Combinatorics.Progressions.Estimates.BoundedInequalityGoodCutoff
import OAI.Combinatorics.Progressions.Estimates.PrincipalCoefficientSource
import OAI.Combinatorics.Progressions.Geometry.BlockCubeCoordinates
import OAI.Combinatorics.Progressions.Sampling.CanonicalSamplerTuple

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weightedCutoff_derivative_pointwise (w θ : E → ℝ)
    (hw : ContDiff ℝ 1 w) (hθ : ContDiff ℝ 1 θ)
    (hrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1) {L : ℝ} (hL : 0 ≤ L)
    (hder : ∀ x ∈ tsupport w, ‖fderiv ℝ θ x‖ ≤ L) (x v : E) :
    |fderiv ℝ (fun y => w y * θ y) x v| ≤
      |fderiv ℝ w x v| + (L * ‖v‖) * |w x| := by
  by_cases hx : x ∈ tsupport w
  · have hd : |fderiv ℝ θ x v| ≤ L * ‖v‖ := by
      have h := ((fderiv ℝ θ x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hder x hx) (norm_nonneg v))
      simpa only [Real.norm_eq_abs] using h
    rw [fderiv_fun_mul (hw.differentiable one_ne_zero x) (hθ.differentiable one_ne_zero x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have ha := abs_add_le (w x * fderiv ℝ θ x v) (θ x * fderiv ℝ w x v)
    simp only [abs_mul, abs_of_nonneg (hrange x).1] at ha
    have hb := mul_le_mul_of_nonneg_left hd (abs_nonneg (w x))
    have hc := mul_le_of_le_one_left (abs_nonneg (fderiv ℝ w x v)) (hrange x).2
    nlinarith
  · have hs : x ∉ tsupport (fun y => w y * θ y) :=
      fun h => hx (tsupport_mul_subset_left h)
    rw [fderiv_of_notMem_tsupport ℝ hs, zero_apply, abs_zero]
    positivity

theorem compact_weight_directional_integrable [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (w : E → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (v : E) :
    Integrable (fun x => |fderiv ℝ w x v|) μ := by
  have hi : Integrable (fun x => fderiv ℝ w x v) μ :=
    ((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hs.fderiv_apply ℝ v)
  simpa only [Real.norm_eq_abs] using hi.norm

theorem weightedCutoff_derivative_integral_le [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (w θ : E → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hθ : ContDiff ℝ 1 θ) (hrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1)
    {L : ℝ} (hL : 0 ≤ L) (hder : ∀ x ∈ tsupport w, ‖fderiv ℝ θ x‖ ≤ L) (v : E) :
    (∫ x, |fderiv ℝ (fun y => w y * θ y) x v| ∂μ) ≤
      (∫ x, |fderiv ℝ w x v| ∂μ) + (L * ‖v‖) * ∫ x, |w x| ∂μ := by
  have hdi := compact_weight_directional_integrable μ w hw hs v
  have hwi : Integrable (fun x => |w x|) μ := by
    simpa only [Real.norm_eq_abs] using (hw.continuous.integrable_of_hasCompactSupport hs (μ := μ)).norm
  have hleft := compact_weight_directional_integrable μ (fun y => w y * θ y)
    (hw.mul hθ) hs.mul_right v
  have h := integral_mono hleft (hdi.add (hwi.const_mul (L * ‖v‖)))
    (fun x => weightedCutoff_derivative_pointwise w θ hw hθ hrange hL hder x v)
  simp only [Pi.add_apply] at h
  rw [integral_add hdi (hwi.const_mul (L * ‖v‖)), integral_const_mul] at h
  exact h

theorem weightedCutoff_abs_mass_le [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (w θ : E → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hθ : ContDiff ℝ 1 θ) (hrange : ∀ x, θ x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, |w x * θ x| ∂μ) ≤ ∫ x, |w x| ∂μ := by
  have hwθ : Integrable (fun x => w x * θ x) μ :=
    (hw.mul hθ).continuous.integrable_of_hasCompactSupport hs.mul_right
  have hwi : Integrable w μ := hw.continuous.integrable_of_hasCompactSupport hs
  have hleft : Integrable (fun x => |w x * θ x|) μ := by
    simpa only [Real.norm_eq_abs] using hwθ.norm
  have hright : Integrable (fun x => |w x|) μ := by
    simpa only [Real.norm_eq_abs] using hwi.norm
  apply integral_mono hleft hright
  intro x
  change |w x * θ x| ≤ |w x|
  rw [abs_mul, abs_of_nonneg (hrange x).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (hrange x).2

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def blockCubeWeight {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (a : BlockParameter B F α → ℝ) : ℝ :=
  w ((blockCubeFlatten B F α).symm a)

theorem blockCubeWeight_contDiff {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) :
    ContDiff ℝ 1 (blockCubeWeight w) := hw.comp (blockCubeFlatten B F α).symm.contDiff

theorem blockCubeWeight_compact {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : HasCompactSupport w) :
    HasCompactSupport (blockCubeWeight w) :=
  hw.comp_homeomorph (blockCubeFlatten B F α).symm.toHomeomorph

theorem blockCubeWeight_tsupport {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    tsupport (blockCubeWeight w) = (blockCubeFlatten B F α).symm ⁻¹' tsupport w :=
  tsupport_comp_eq_preimage w (blockCubeFlatten B F α).symm.toHomeomorph

theorem blockCubeWeight_integral {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    (∫ a, blockCubeWeight w a) = ∫ x, w x :=
  (blockCubeFlatten_symm_measurePreserving B F α).integral_comp
    (blockCubeFlatten B F α).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding w

theorem blockCubeWeight_abs_integral {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) :
    (∫ a, |blockCubeWeight w a|) = ∫ x, |w x| :=
  blockCubeWeight_integral (fun x => |w x|)

theorem blockCubeWeight_coordinate_fderiv {B F α : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] [Fintype α] [DecidableEq α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w)
    (a : BlockParameter B F α → ℝ) (b : B) (f : F) (r : Option α) :
    fderiv ℝ (blockCubeWeight w) a (Pi.single (b, f, r) 1) =
      fderiv ℝ w ((blockCubeFlatten B F α).symm a) (Pi.single (b, f) (Pi.single r 1)) := by
  have hd := (hw.differentiable one_ne_zero ((blockCubeFlatten B F α).symm a)).hasFDerivAt.comp a
    (blockCubeFlatten B F α).symm.toContinuousLinearMap.hasFDerivAt
  change fderiv ℝ (w ∘ (blockCubeFlatten B F α).symm) a (Pi.single (b, f, r) 1) = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv ℝ w ((blockCubeFlatten B F α).symm a)) (blockCubeFlatten_symm_single b f r)

theorem blockCubeWeight_coordinate_integral {B F α : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] [Fintype α] [DecidableEq α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w)
    (b : B) (f : F) (r : Option α) :
    (∫ a, |fderiv ℝ (blockCubeWeight w) a (Pi.single (b, f, r) 1)|) =
      ∫ x, |fderiv ℝ w x (Pi.single (b, f) (Pi.single r 1))| := by
  simp_rw [blockCubeWeight_coordinate_fderiv w hw]
  exact blockCubeWeight_integral (fun x => |fderiv ℝ w x (Pi.single (b, f) (Pi.single r 1))|)

theorem blockCubeWeight_derivative_sum {B F α : Type*} [Fintype B] [DecidableEq B]
    [Fintype F] [DecidableEq F] [Fintype α] [DecidableEq α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) :
    (∑ z : BlockParameter B F α, ∫ a, |fderiv ℝ (blockCubeWeight w) a (Pi.single z 1)|) =
      ∑ bf : B × F, ∑ r : Option α, ∫ x, |fderiv ℝ w x (Pi.single bf (Pi.single r 1))| := by
  simp only [Fintype.sum_prod_type, blockCubeWeight_coordinate_integral w hw]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def blockCubeMeasure (B F α : Type*) [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] : Measure (BlockParameter B F α → ℝ) :=
  Measure.map (blockCubeFlatten B F α) (scalarCubeProductMeasure (B × F) α)

instance blockCubeMeasure_probability (B F α : Type*) [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] : IsProbabilityMeasure (blockCubeMeasure B F α) := by
  constructor
  rw [blockCubeMeasure, Measure.map_apply (blockCubeFlatten B F α).continuous.measurable
    MeasurableSet.univ, Set.preimage_univ, measure_univ]

theorem blockCubeMeasure_integral {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] (f : (BlockParameter B F α → ℝ) → ℝ) :
    (∫ a, f a ∂blockCubeMeasure B F α) =
      ∫ x, f (blockCubeFlatten B F α x) ∂scalarCubeProductMeasure (B × F) α :=
  (blockCubeFlatten B F α).toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map f

theorem blockCubeMeasure_real_apply {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] (s : Set (BlockParameter B F α → ℝ)) (hs : MeasurableSet s) :
    (blockCubeMeasure B F α).real s =
      (scalarCubeProductMeasure (B × F) α).real (blockCubeFlatten B F α ⁻¹' s) := by
  rw [measureReal_def, blockCubeMeasure,
    Measure.map_apply (blockCubeFlatten B F α).continuous.measurable hs]
  rfl

theorem blockCubeFlatten_box {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] {x : (B × F) → Option α → ℝ} (hx : x ∈ scalarCubeProductDomain (B × F) α)
    (z : BlockParameter B F α) : |blockCubeFlatten B F α x z| ≤ 1 :=
  (scalarCubeDomain_coordinate_abs_lt_one (hx (z.1, z.2.1) (Set.mem_univ _)) z.2.2).le

theorem blockCubeWeight_box {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    [DecidableEq α] (w : ((B × F) → Option α → ℝ) → ℝ)
    (hs : tsupport w ⊆ scalarCubeProductDomain (B × F) α)
    {a : BlockParameter B F α → ℝ} (ha : a ∈ tsupport (blockCubeWeight w))
    (z : BlockParameter B F α) : |a z| ≤ 1 := by
  rw [blockCubeWeight_tsupport] at ha
  have hx := blockCubeFlatten_box (hs ha) z
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem blockCubeWeight_integral_test {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
    (w : ((B × F) → Option α → ℝ) → ℝ) (f : (BlockParameter B F α → ℝ) → ℝ) :
    (∫ a, blockCubeWeight w a * f a) =
      ∫ x, w x * f (blockCubeFlatten B F α x) := by
  have h := (blockCubeFlatten_measurePreserving B F α).integral_comp
    (blockCubeFlatten B F α).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun a => blockCubeWeight w a * f a)
  simp only [blockCubeWeight, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

noncomputable def booleanCubeDeterminant {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (x : (B × F) → Option α → ℝ) : ℝ :=
  booleanMinorDeterminant c sets block v r (blockCubeFlatten B F α x)

theorem booleanCubeDeterminant_contDiff {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α) :
    ContDiff ℝ ∞ (booleanCubeDeterminant c sets block v r) :=
  (booleanMinorDeterminant_contDiff c sets block v r).comp (blockCubeFlatten B F α).contDiff

theorem booleanCubeDeterminant_fderiv_norm_le {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ o, |c (block o)| ≤ C)
    (x : (B × Fin h) → Option α → ℝ) (hx : x ∈ scalarCubeProductDomain (B × Fin h) α) :
    ‖fderiv ℝ (booleanCubeDeterminant c sets block v r) x‖ ≤
      productMinorDeterminantDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C 1 := by
  let e := (blockCubeFlatten B (Fin h) α).toContinuousLinearMap
  have hd := ((booleanMinorDeterminant_contDiff c sets block v r).differentiable
    (by norm_num) (e x)).hasFDerivAt
  have he := (hd.comp x e.hasFDerivAt).fderiv
  change fderiv ℝ (booleanCubeDeterminant c sets block v r) x = _ at he
  rw [he]
  calc
    _ ≤ ‖fderiv ℝ (booleanMinorDeterminant c sets block v r) (e x)‖ * ‖e‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (booleanMinorDeterminant c sets block v r) (e x)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (blockCubeFlatten_norm_le_one B (Fin h) α)
    _ ≤ _ := booleanMinorDeterminant_fderiv_norm_le c sets block v r hcard (e x)
      hC le_rfl hc (blockCubeFlatten_box hx)

theorem booleanCubeDeterminant_sublevel_probability {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α) (u : ℝ) :
    (scalarCubeProductMeasure (B × F) α).real {x | |booleanCubeDeterminant c sets block v r x| < u} =
      (blockCubeMeasure B F α).real {a | |booleanMinorDeterminant c sets block v r a| < u} := by
  symm
  exact blockCubeMeasure_real_apply _ (measurableSet_lt
    (booleanMinorDeterminant_contDiff c sets block v r).continuous.measurable.abs measurable_const)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

def blockCubeScale {B F α : Type*} (T : B × F → ℝ)
    (x : BlockParameter B F α → ℝ) (j : BlockParameter B F α) : ℝ :=
  T (j.1, j.2.1) * x j

theorem blockCubeScale_measurable {B F α : Type*} (T : B × F → ℝ) :
    Measurable (blockCubeScale (α := α) T) :=
  Measurable.of_eval (fun index => measurable_const.mul (measurable_pi_apply index))

noncomputable def scaledBlockCubeMeasure {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α] (T : B × F → ℝ) :
    Measure (BlockParameter B F α → ℝ) :=
  (scaledCubeProductMeasure α T).map (blockCubeFlatten B F α)

theorem scaledBlockCubeMeasure_eq_map {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α] (T : B × F → ℝ) (hT : ∀ i, 0 < T i) :
    scaledBlockCubeMeasure (α := α) T =
      (blockCubeMeasure B F α).map (blockCubeScale T) := by
  have hm : Measurable (fun x : (B × F) → Option α → ℝ => fun i => T i • x i) :=
    Measurable.of_eval (fun index => (measurable_pi_apply index).const_smul (T index))
  rw [scaledBlockCubeMeasure, scaledCubeProductMeasure_eq_map T hT,
    blockCubeMeasure, Measure.map_map (blockCubeFlatten B F α).continuous.measurable hm,
    Measure.map_map (blockCubeScale_measurable T) (blockCubeFlatten B F α).continuous.measurable]
  rfl

theorem scaledBlockCubeMeasure_probability {B F α : Type*} [Fintype B] [Fintype F]
    [Fintype α] [DecidableEq α] (T : B × F → ℝ) (hT : ∀ i, 0 < T i) :
    IsProbabilityMeasure (scaledBlockCubeMeasure (α := α) T) := by
  rw [scaledBlockCubeMeasure_eq_map T hT]
  infer_instance

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

noncomputable def scalarCubeGoodWeight {I J : Type*} [Fintype I] [Fintype J]
    (α : Type*) [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (r : I → ℝ) (κ : J → ℝ)
    (d : J → (I → Option α → ℝ) → ℝ) (x : I → Option α → ℝ) : ℝ :=
  scalarCubeProductWeight α r x * sublevelCutoffProduct ψ κ d x

theorem scalarCubeGoodWeight_spec {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → (I → Option α → ℝ) → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    ContDiff ℝ 1 (scalarCubeGoodWeight α ψ r κ d) ∧
      HasCompactSupport (scalarCubeGoodWeight α ψ r κ d) ∧
      tsupport (scalarCubeGoodWeight α ψ r κ d) ⊆
        scalarCubeProductDomain I α ∩ {x | ∀ i, κ i ≤ |d i x|} ∧
      (∀ x, 0 ≤ scalarCubeGoodWeight α ψ r κ d x) ∧
      (∫ x, |scalarCubeGoodWeight α ψ r κ d x|) ≤ 1 := by
  have hb := scalarCubeProductWeight_spec (α := α) r hr
  have hθ : ContDiff ℝ 1 (sublevelCutoffProduct ψ κ d) :=
    (sublevelCutoffProduct_smooth ψ hψ κ d hd).of_le (by norm_num)
  refine ⟨hb.1.mul hθ, hb.2.1.mul_right, ?_, ?_, ?_⟩
  · intro x hx
    have h := goodDomainCutoff_tsupport_subset ψ hzero κ hκ d
      (fun i => (hd i).continuous) (scalarCubeProductWeight α r) hx
    exact ⟨hb.2.2.1 h.1, h.2⟩
  · intro x
    exact mul_nonneg (hb.2.2.2.1 x) (sublevelCutoffProduct_range ψ hrange κ d x).1
  · exact (weightedCutoff_abs_mass_le volume _ _ hb.1 hb.2.1 hθ
      (sublevelCutoffProduct_range ψ hrange κ d)).trans hb.2.2.2.2

theorem scalarCubeGoodWeight_integral_test {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (κ : J → ℝ) (d : J → (I → Option α → ℝ) → ℝ) (f : (I → Option α → ℝ) → ℝ) :
    (∫ x, scalarCubeGoodWeight α ψ r κ d x * f x) =
      ∫ x, goodDomainCutoff ψ κ d (scalarCubeProductCutoff α r) x * f x
        ∂scalarCubeProductMeasure I α := by
  have h := scalarCubeProductWeight_integral_test r hr
    (fun x => sublevelCutoffProduct ψ κ d x * f x)
  simpa only [scalarCubeGoodWeight, sublevelCutoffProduct, goodDomainCutoff, mul_assoc] using h

theorem scalarCubeGoodWeight_mass_lower {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → (I → Option α → ℝ) → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) :
    1 - scalarCubeBoundaryConstant α * ∑ i, r i -
        ∑ i, (scalarCubeProductMeasure I α).real {x | |d i x| < 2 * κ i} ≤
      ∫ x, scalarCubeGoodWeight α ψ r κ d x := by
  let b := scalarCubeProductCutoff α r
  have hb : ContDiff ℝ ∞ b := scalarCubeProductCutoff_smooth r
  have hbr : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1 := scalarCubeProductCutoff_range r
  have hχ := goodDomainCutoff_smooth ψ hψ κ d hd b hb
  have hχi := cutoff_integrable (scalarCubeProductMeasure I α) _ hχ.continuous.measurable
    (goodDomainCutoff_range ψ hrange κ d b hbr)
  have hl := goodDomainCutoff_integral_loss_le (scalarCubeProductMeasure I α) ψ
    hψ.continuous.measurable hrange hone κ hκ d (fun i => (hd i).continuous.measurable)
    b hb.continuous.measurable hbr
  rw [integral_sub (integrable_const (1 : ℝ)) hχi] at hl
  simp only [integral_const, probReal_univ, one_smul] at hl
  have he := scalarCubeGoodWeight_integral_test ψ r hr κ d (fun _ => 1)
  simp only [mul_one] at he
  rw [← he] at hl
  have hboundary := scalarCubeProductCutoff_mass_loss (α := α) r hr
  change (∫ x, 1 - b x ∂scalarCubeProductMeasure I α) ≤ _ at hboundary
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem restrictBlockParameters_measurable {B O F α : Type*} (block : O → B) :
    Measurable (restrictBlockParameters (F := F) (α := α) block) := by
  unfold restrictBlockParameters
  fun_prop

theorem restrictBlockParameters_cube_measurePreserving {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α] [DecidableEq α]
    (block : O → B) (hblock : Function.Injective block) :
    MeasurePreserving (restrictBlockParameters (F := F) (α := α) block)
      (blockCubeMeasure B F α) (blockCubeMeasure O F α) := by
  let e : O × F → B × F := fun z => (block z.1, z.2)
  have he : Function.Injective e := by
    intro x y hxy
    exact Prod.ext (hblock (congrArg (fun z : B × F => z.1) hxy))
      (congrArg (fun z : B × F => z.2) hxy)
  have hsel := finiteProductMarginal_measurePreserving
    (fun _ : B × F => scalarCubeMeasure α) e he
  change MeasurePreserving _ (scalarCubeProductMeasure (B × F) α)
    (scalarCubeProductMeasure (O × F) α) at hsel
  refine ⟨restrictBlockParameters_measurable block, ?_⟩
  change Measure.map (restrictBlockParameters block)
      (Measure.map (blockCubeFlatten B F α) (scalarCubeProductMeasure (B × F) α)) =
    Measure.map (blockCubeFlatten O F α) (scalarCubeProductMeasure (O × F) α)
  rw [Measure.map_map (restrictBlockParameters_measurable block)
    (blockCubeFlatten B F α).continuous.measurable]
  have hcomp : restrictBlockParameters block ∘ blockCubeFlatten B F α =
      blockCubeFlatten O F α ∘ (fun x : (B × F) → Option α → ℝ => fun z => x (e z)) := rfl
  rw [hcomp, ← Measure.map_map (blockCubeFlatten O F α).continuous.measurable hsel.measurable]
  exact congrArg (Measure.map (blockCubeFlatten O F α)) hsel.map_eq

theorem booleanMinorDeterminant_restrict {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) :
    booleanMinorDeterminant c sets block v r a =
      booleanMinorDeterminant (c ∘ block) sets id v r (restrictBlockParameters block a) :=
  congrArg Matrix.det (booleanSelectedMinor_restrict_eval c sets block v r a)

theorem booleanMinorDeterminant_sublevel_marginal {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (hblock : Function.Injective block)
    (v : F) (r : O → Option α) (u : ℝ) :
    (blockCubeMeasure B F α).real {a | |booleanMinorDeterminant c sets block v r a| ≤ u} =
      (blockCubeMeasure O F α).real {a | |booleanMinorDeterminant (c ∘ block) sets id v r a| ≤ u} := by
  have hs : MeasurableSet {a | |booleanMinorDeterminant (c ∘ block) sets id v r a| ≤ u} :=
    measurableSet_le (booleanMinorDeterminant_contDiff (c ∘ block) sets id v r).continuous.measurable.abs
      measurable_const
  have hm := (restrictBlockParameters_cube_measurePreserving (F := F) (α := α) block hblock).measureReal_preimage
    hs.nullMeasurableSet
  simpa only [Set.preimage_setOf_eq, ← booleanMinorDeterminant_restrict] using hm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem scalarCubeGoodWeight_directional_le {I J α : Type*} [Fintype I] [Fintype J]
    [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (A : ℝ≥0) (hLip : LipschitzWith A ψ)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → (I → Option α → ℝ) → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (L : J → ℝ≥0)
    (hder : ∀ i x, x ∈ scalarCubeProductDomain I α → ‖fderiv ℝ (d i) x‖ ≤ L i)
    (v : I → Option α → ℝ) :
    (∫ x, |fderiv ℝ (scalarCubeGoodWeight α ψ r κ d) x v|) ≤
      (∫ x, |fderiv ℝ (scalarCubeProductWeight α r) x v|) +
        (∑ i, (A : ℝ) / κ i * L i) * ‖v‖ := by
  have hb := scalarCubeProductWeight_spec (α := α) r hr
  have hθ : ContDiff ℝ 1 (sublevelCutoffProduct ψ κ d) :=
    (sublevelCutoffProduct_smooth ψ hψ κ d hd).of_le (by norm_num)
  have hS : 0 ≤ ∑ i, (A : ℝ) / κ i * L i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (div_nonneg A.coe_nonneg (hκ i).le) (L i).coe_nonneg)
  have hθbound (x) (hx : x ∈ tsupport (scalarCubeProductWeight α r)) :
      ‖fderiv ℝ (sublevelCutoffProduct ψ κ d) x‖ ≤ ∑ i, (A : ℝ) / κ i * L i :=
    (sublevelCutoffProduct_fderiv_norm_le ψ hψ hrange A hLip κ hκ d hd x).trans
      (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (hder i x (hb.2.2.1 hx)) (div_nonneg A.coe_nonneg (hκ i).le)))
  have h := weightedCutoff_derivative_integral_le volume _ _ hb.1 hb.2.1 hθ
    (sublevelCutoffProduct_range ψ hrange κ d) hS hθbound v
  exact h.trans (add_le_add le_rfl
    (mul_le_of_le_one_right (mul_nonneg hS (norm_nonneg v)) hb.2.2.2.2))

theorem scalarCubeGoodWeight_derivative_budget {I J α : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [Fintype α] [DecidableEq α] (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (A T : ℝ≥0)
    (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (d : J → (I → Option α → ℝ) → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (L : J → ℝ≥0)
    (hder : ∀ i x, x ∈ scalarCubeProductDomain I α → ‖fderiv ℝ (d i) x‖ ≤ L i) :
    (∑ i, ∑ j : Option α, ∫ x,
      |fderiv ℝ (scalarCubeGoodWeight α ψ r κ d) x (Pi.single i (Pi.single j 1))|) ≤
      (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r i) +
        (Fintype.card I : ℝ) * ((Fintype.card α : ℝ) + 1) *
          (∑ i, (A : ℝ) / κ i * L i) := by
  let S := ∑ i, (A : ℝ) / κ i * L i
  have hcoord (i : I) (j : Option α) :
      (∫ x, |fderiv ℝ (scalarCubeGoodWeight α ψ r κ d) x (Pi.single i (Pi.single j 1))|) ≤
        (∫ x, |fderiv ℝ (scalarCubeProductWeight α r) x (Pi.single i (Pi.single j 1))|) + S := by
    have h := scalarCubeGoodWeight_directional_le ψ hψ hrange A hLip r hr κ hκ d hd L hder
      (Pi.single i (Pi.single j 1))
    simpa only [Pi.norm_single, norm_one, mul_one] using h
  calc
    _ ≤ ∑ i, ∑ j : Option α,
        ((∫ x, |fderiv ℝ (scalarCubeProductWeight α r) x (Pi.single i (Pi.single j 1))|) + S) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcoord i j))
    _ = (∑ i, ∑ j : Option α,
        ∫ x, |fderiv ℝ (scalarCubeProductWeight α r) x (Pi.single i (Pi.single j 1))|) +
        (Fintype.card I : ℝ) * ((Fintype.card α : ℝ) + 1) * S := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Fintype.card_option, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ _ := add_le_add (scalarCubeProductWeight_derivative_budget (α := α) r hr T hTransition) le_rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

noncomputable def booleanCubeGoodWeight {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B) {h : ℕ}
    (v : Fin h) (sel : J → O → Option α) (ψ : ℝ → ℝ)
    (r : B × Fin h → ℝ) (κ : J → ℝ) : (BlockParameter B (Fin h) α → ℝ) → ℝ :=
  blockCubeWeight (scalarCubeGoodWeight α ψ r κ
    (fun j => booleanCubeDeterminant (c j) sets (block j) v (sel j)))

theorem booleanCubeGoodWeight_spec {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B) {h : ℕ}
    (v : Fin h) (sel : J → O → Option α) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i) :
    let w := booleanCubeGoodWeight c sets block v sel ψ r κ
    ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ (∀ a, 0 ≤ w a) ∧ (∫ a, |w a|) ≤ 1 ∧
      ∀ a ∈ tsupport w, (∀ z, |a z| ≤ 1) ∧
        ∀ j, κ j ≤ |booleanMinorDeterminant (c j) sets (block j) v (sel j) a| := by
  let d := fun j => booleanCubeDeterminant (c j) sets (block j) v (sel j)
  have hd := fun j => booleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j)
  have hs := scalarCubeGoodWeight_spec ψ hψ hrange hzero r hr κ hκ d hd
  refine ⟨blockCubeWeight_contDiff _ hs.1, blockCubeWeight_compact _ hs.2.1,
    fun a => hs.2.2.2.1 _, ?_, ?_⟩
  · change (∫ a, |blockCubeWeight (scalarCubeGoodWeight α ψ r κ d) a|) ≤ 1
    rw [blockCubeWeight_abs_integral]
    exact hs.2.2.2.2
  · intro a ha
    refine ⟨blockCubeWeight_box _ (fun x hx => (hs.2.2.1 hx).1) ha, ?_⟩
    change a ∈ tsupport (blockCubeWeight (scalarCubeGoodWeight α ψ r κ d)) at ha
    rw [blockCubeWeight_tsupport] at ha
    intro j
    have hj := (hs.2.2.1 ha).2 j
    change κ j ≤ |booleanMinorDeterminant (c j) sets (block j) v (sel j)
      (blockCubeFlatten B (Fin h) α ((blockCubeFlatten B (Fin h) α).symm a))| at hj
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hj

theorem booleanCubeGoodWeight_mass_lower {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B) {h : ℕ}
    (v : Fin h) (sel : J → O → Option α) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i) :
    1 - scalarCubeBoundaryConstant α * ∑ i, r i -
        ∑ j, (blockCubeMeasure B (Fin h) α).real
          {a | |booleanMinorDeterminant (c j) sets (block j) v (sel j) a| < 2 * κ j} ≤
      ∫ a, booleanCubeGoodWeight c sets block v sel ψ r κ a := by
  unfold booleanCubeGoodWeight
  rw [blockCubeWeight_integral]
  have hs := scalarCubeGoodWeight_mass_lower ψ hψ hrange hone r hr κ hκ
    (fun j => booleanCubeDeterminant (c j) sets (block j) v (sel j))
    (fun j => booleanCubeDeterminant_contDiff (c j) sets (block j) v (sel j))
  simp_rw [booleanCubeDeterminant_sublevel_probability] at hs
  exact hs

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

noncomputable def jointBooleanGoodWeight {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (ψ : ℝ → ℝ)
    (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ) : (JointBlockParameter B h α → ℝ) → ℝ :=
  sigmaAxisWeight (fun d => booleanCubeGoodWeight (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) ψ (r d) (fun _ => κ d))

theorem jointBooleanGoodWeight_spec {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) :
    let w := jointBooleanGoodWeight c sets block v sel ψ r κ
    ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧ (∫ x, |w x|) ≤ 1 ∧
      ∀ x ∈ tsupport w, (∀ s, |x s| ≤ 1) ∧ ∀ d, κ d ≤
        |booleanMinorDeterminant (c d) (sets d) (block d) (v d) (sel d) (fun i => x ⟨d, i⟩)| := by
  have hs (d : D) := booleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) ψ hψ hrange hzero (r d) (hr d)
    (fun _ => κ d) (fun _ => hκ d)
  refine ⟨sigmaAxisWeight_contDiff _ (fun d => (hs d).1),
    sigmaAxisWeight_compact _ (fun d => (hs d).2.1),
    sigmaAxisWeight_nonneg _ (fun d => (hs d).2.2.1),
    sigmaAxisWeight_abs_mass_le_one _ (fun d => (hs d).2.2.2.1), ?_⟩
  intro x hx
  have hp (d : D) := (hs d).2.2.2.2 _ (sigmaAxisWeight_tsupport _ hx d)
  exact ⟨fun s => (hp s.1).1 s.2, fun d => (hp d).2 ()⟩

end Erdos3

end

end OAI
