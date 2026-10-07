/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Construct mapped probability instances explicitly from measurability.
Mathematical statements unchanged. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.JointBooleanGoodWeight
import OAI.Combinatorics.Progressions.Geometry.UnitBoxInteriorCutoff
import OAI.Combinatorics.Progressions.Probability.SigmaProductMeasure
import OAI.Combinatorics.Progressions.Probability.SpatialProductDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

omit [MeasurableNeg G] in
theorem realDensityMeasure_map_add_right (μ : Measure G) [μ.IsAddLeftInvariant]
    (f : G → ℝ) (a : G) :
    (realDensityMeasure μ f).map (fun u => u + a) =
      realDensityMeasure μ (fun y => f (y - a)) := by
  have h := realDensityMeasure_map_equiv (MeasurableEquiv.addRight a) μ f
  simpa only [MeasurableEquiv.symm_addRight, MeasurableEquiv.coe_addRight,
    map_add_right_eq_self, sub_eq_add_neg] using h

theorem haarShiftDensity_image_law (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1) :
    (ν.prod (realDensityMeasure μ f)).map (fun p => p.2 + z p.1) =
      realDensityMeasure μ (haarShiftDensity ν z f) := by
  let _ := realDensityMeasure_probability μ f hfi hf0 hmass
  apply densityMixture_image_law ν (realDensityMeasure μ f) μ _
    (measurable_snd.add (hz.comp measurable_fst)) (fun t y => f (y - z t))
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · exact fun t => ⟨fun y => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩
  · exact fun t => realDensityMeasure_map_add_right μ f (z t)

theorem realDensityMeasure_le_of_cap {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {C : ℝ} (hcap : ∀ x, f x ≤ C) :
    realDensityMeasure μ f ≤ ENNReal.ofReal C • μ := by
  change μ.withDensity (fun x => ENNReal.ofReal (f x)) ≤ _
  rw [← withDensity_const]
  exact withDensity_mono (ae_of_all μ (fun x => ENNReal.ofReal_le_ofReal (hcap x)))

theorem haarShiftDensity_image_le (μ : Measure G) [μ.IsAddLeftInvariant] [SFinite μ]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    (hfi : Integrable f μ) {C : ℝ} (hcap : ∀ x, f x ∈ Set.Icc (0 : ℝ) C)
    (hmass : (∫ x, f x ∂μ) = 1) :
    (ν.prod (realDensityMeasure μ f)).map (fun p => p.2 + z p.1) ≤ ENNReal.ofReal C • μ := by
  rw [haarShiftDensity_image_law μ ν hz hf hfi (fun x => (hcap x).1) hmass]
  exact realDensityMeasure_le_of_cap μ _ (fun y => (haarShiftDensity_cap ν hz hf hcap y).2)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

noncomputable def sigmaAxisMeasure (μ : ∀ d, Measure (I d → ℝ)) : Measure ((Σ d, I d) → ℝ) :=
  Measure.map (sigmaAxisCoordinates I).symm (Measure.pi μ)

instance sigmaAxisMeasure_probability (μ : ∀ d, Measure (I d → ℝ))
    [∀ d, IsProbabilityMeasure (μ d)] : IsProbabilityMeasure (sigmaAxisMeasure μ) := by
  unfold sigmaAxisMeasure
  exact Measure.isProbabilityMeasure_map
    (sigmaAxisCoordinates I).symm.continuous.measurable.aemeasurable

theorem sigmaAxisMeasure_projection (μ : ∀ d, Measure (I d → ℝ))
    [∀ d, IsProbabilityMeasure (μ d)] (d : D) :
    MeasurePreserving (sigmaAxisProjection I d) (sigmaAxisMeasure μ) (μ d) := by
  refine ⟨(sigmaAxisProjection I d).continuous.measurable, ?_⟩
  rw [sigmaAxisMeasure, Measure.map_map (sigmaAxisProjection I d).continuous.measurable
    (sigmaAxisCoordinates I).symm.continuous.measurable]
  exact (measurePreserving_eval μ d).map_eq

theorem sigmaAxisMeasure_integral (μ : ∀ d, Measure (I d → ℝ))
    (f : ((Σ d, I d) → ℝ) → ℝ) :
    (∫ x, f x ∂sigmaAxisMeasure μ) =
      ∫ x, f ((sigmaAxisCoordinates I).symm x) ∂Measure.pi μ :=
  (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map f

omit [∀ d, Fintype (O d)] in
theorem sigmaAxisSampler_measurable (U : ∀ d, (I d → ℝ) → (O d → ℝ))
    (hU : ∀ d, Measurable (U d)) : Measurable (sigmaAxisSampler U) :=
  Measurable.of_eval (fun s => (measurable_pi_apply s.2).comp
    ((hU s.1).comp (sigmaAxisProjection I s.1).continuous.measurable))

theorem sigmaAxisSampler_image_law (μ : ∀ d, Measure (I d → ℝ))
    [∀ d, IsProbabilityMeasure (μ d)]
    (U : ∀ d, (I d → ℝ) → (O d → ℝ)) (hU : ∀ d, Measurable (U d)) :
    Measure.map (sigmaAxisSampler U) (sigmaAxisMeasure μ) =
      sigmaAxisMeasure (fun d => Measure.map (U d) (μ d)) := by
  let : ∀ d, IsProbabilityMeasure (Measure.map (U d) (μ d)) :=
    fun d => Measure.isProbabilityMeasure_map (hU d).aemeasurable
  rw [sigmaAxisMeasure, Measure.map_map (sigmaAxisSampler_measurable U hU)
    (sigmaAxisCoordinates I).symm.continuous.measurable]
  have he : sigmaAxisSampler U ∘ (sigmaAxisCoordinates I).symm =
      (sigmaAxisCoordinates O).symm ∘ (fun x d => U d (x d)) := rfl
  have hPi : Measurable (fun x : ∀ d, I d → ℝ => fun d => U d (x d)) :=
    Measurable.of_eval (fun d => (hU d).comp (measurable_pi_apply d))
  rw [he, ← Measure.map_map (sigmaAxisCoordinates O).symm.continuous.measurable
    hPi]
  rw [Measure.pi_map_pi (fun d => (hU d).aemeasurable)]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

theorem sigmaAxisMeasure_withDensity (μ : ∀ d, Measure (I d → ℝ)) [∀ d, SigmaFinite (μ d)]
    (f : ∀ d, (I d → ℝ) → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hf0 : ∀ d x, 0 ≤ f d x) :
    sigmaAxisMeasure (fun d => realDensityMeasure (μ d) (f d)) =
      realDensityMeasure (sigmaAxisMeasure μ) (sigmaAxisWeight f) := by
  unfold sigmaAxisMeasure
  rw [realDensityMeasure_pi μ f hf hf0]
  exact realDensityMeasure_map_equiv
    (sigmaAxisCoordinates I).symm.toHomeomorph.toMeasurableEquiv _ _

theorem sigmaAxisMeasure_volume :
    sigmaAxisMeasure (fun d => (volume : Measure (I d → ℝ))) = volume :=
  (sigmaAxisCoordinates_symm_measurePreserving I).map_eq

theorem sigmaAxisMeasure_density (f : ∀ d, (I d → ℝ) → ℝ)
    (hf : ∀ d, Integrable (f d)) (hf0 : ∀ d x, 0 ≤ f d x) :
    sigmaAxisMeasure (fun d => realDensityMeasure volume (f d)) =
      realDensityMeasure volume (sigmaAxisWeight f) := by
  rw [sigmaAxisMeasure_withDensity _ f hf hf0, sigmaAxisMeasure_volume]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem sigmaAxisMeasure_unitBox {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)] :
    sigmaAxisMeasure (fun d => unitBoxMeasure (I d)) = unitBoxMeasure (Σ d, I d) := by
  unfold sigmaAxisMeasure
  simp_rw [unitBoxMeasure_eq_pi]
  exact sigmaProductMeasure_flatten (fun _ : Σ d, I d => unitScalarMeasure)

theorem realDensityMeasure_unit_lift (f : ℝ → ℝ) :
    (realDensityMeasure volume f).map (fun x (_ : Unit) => x) =
      realDensityMeasure volume (fun v : Unit → ℝ => f (v ())) := by
  have hvol := (volume_preserving_funUnique Unit ℝ).symm (MeasurableEquiv.funUnique Unit ℝ)
  have he := realDensityMeasure_map_equiv (MeasurableEquiv.funUnique Unit ℝ).symm volume f
  rw [hvol.map_eq] at he
  exact he

theorem unit_lift_integral (f : ℝ → ℝ) :
    (∫ v : Unit → ℝ, f (v ())) = ∫ x, f x :=
  (volume_preserving_funUnique Unit ℝ).integral_comp (MeasurableEquiv.funUnique Unit ℝ).measurableEmbedding f

theorem scalarJoint_image_density
    {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]
    (F : ∀ d, (I d → ℝ) → ℝ) (hF : ∀ d, Measurable (F d)) (f : D → ℝ → ℝ)
    (_hf : ∀ d, Integrable (f d)) (hf0 : ∀ d x, 0 ≤ f d x) (hfm : ∀ d, (∫ x, f d x) = 1)
    (hlaw : ∀ d, (unitBoxMeasure (I d)).map (F d) = realDensityMeasure volume (f d))
    (shift : D → ℝ) :
    (unitBoxMeasure (Σ d, I d)).map
        (fun x (o : Σ _d : D, Unit) => shift o.1 + F o.1 (fun i => x ⟨o.1, i⟩)) =
      realDensityMeasure volume
        (sigmaAxisWeight (fun d (v : Unit → ℝ) => f d (v () - shift d))) := by
  let U := fun d (x : I d → ℝ) (_ : Unit) => shift d + F d x
  have hU (d) : Measurable (U d) := Measurable.of_eval (fun _ => measurable_const.add (hF d))
  have hsingle (d) : (unitBoxMeasure (I d)).map (U d) =
      realDensityMeasure volume (fun v : Unit → ℝ => f d (v () - shift d)) := by
    have ha : Measurable (fun x : ℝ => x + shift d) := measurable_id.add measurable_const
    have hc : Measurable (fun x : ℝ => fun _ : Unit => x) := Measurable.of_eval (fun _ => measurable_id)
    rw [← realDensityMeasure_unit_lift (fun y => f d (y - shift d)), ← realDensityMeasure_map_add_right,
      ← hlaw d, Measure.map_map ha (hF d), Measure.map_map hc (ha.comp (hF d))]
    congr 1
    funext x u
    exact add_comm _ _
  have hi (d) : Integrable (fun v : Unit → ℝ => f d (v () - shift d)) := by
    apply Integrable.of_integral_ne_zero
    rw [unit_lift_integral (fun y => f d (y - shift d)), integral_sub_right_eq_self, hfm d]
    exact one_ne_zero
  rw [← sigmaAxisMeasure_unitBox I]
  change (sigmaAxisMeasure (fun d => unitBoxMeasure (I d))).map (sigmaAxisSampler U) = _
  rw [sigmaAxisSampler_image_law _ U hU]
  simp_rw [hsingle]
  exact sigmaAxisMeasure_density _ hi (fun d v => hf0 d _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

noncomputable def principalProductValue (c : B → ℝ) (x : B × F → ℝ) : ℝ :=
  ∑ b, c b * ∏ k, x (b, k)

omit [DecidableEq B] [DecidableEq F] in
theorem principalProductValue_measurable [DecidableEq B] [DecidableEq F] (c : B → ℝ) :
    Measurable (principalProductValue (F := F) c) := by
  unfold principalProductValue
  fun_prop

noncomputable def booleanOneCubeEndpoints (c : B → ℝ)
    (a : BlockParameter B F (Fin 1) → ℝ) : ℝ × ℝ :=
  (booleanSamplerMap c id a ∅,
    booleanSamplerMap c id a ∅ + booleanSamplerMap c id a {0})

omit [DecidableEq B] [DecidableEq F] in
theorem booleanOneCubeEndpoints_eq [DecidableEq B] [DecidableEq F]
    (c : B → ℝ) (a : BlockParameter B F (Fin 1) → ℝ) :
    booleanOneCubeEndpoints c a =
      (principalProductValue c (fun i => a (i.1, i.2, none)),
        principalProductValue c (fun i => a (i.1, i.2, none) + a (i.1, i.2, some 0))) := by
  have hpow : ({0} : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  simp [booleanOneCubeEndpoints, booleanSamplerMap_formula, booleanCoefficient,
    hpow, principalProductValue, Fintype.sum_option, booleanFeature]

theorem booleanOneCubeEndpoints_measurable (c : B → ℝ) :
    Measurable (booleanOneCubeEndpoints (F := F) c) := by
  change Measurable (fun a => booleanOneCubeEndpoints (F := F) c a)
  simp_rw [booleanOneCubeEndpoints_eq]
  exact ((principalProductValue_measurable c).comp (by fun_prop)).prodMk
    ((principalProductValue_measurable c).comp (by fun_prop))

theorem booleanOneCubeEndpoints_image (c : B → ℝ) :
    (blockCubeMeasure B F (Fin 1)).map (booleanOneCubeEndpoints c) =
      ((unitBoxMeasure (B × F)).map (principalProductValue c)).prod
        ((unitBoxMeasure (B × F)).map (principalProductValue c)) := by
  rw [blockCubeMeasure,
    Measure.map_map (booleanOneCubeEndpoints_measurable c)
      (blockCubeFlatten B F (Fin 1)).continuous.measurable]
  have he : booleanOneCubeEndpoints c ∘ blockCubeFlatten B F (Fin 1) =
      (fun a => (principalProductValue c (fun i => a i none),
        principalProductValue c (fun i => a i none + a i (some 0)))) := by
    funext a
    rw [Function.comp_apply, booleanOneCubeEndpoints_eq]
    rfl
  rw [he]
  exact scalarOneCube_product_image (B × F) (principalProductValue c)
    (principalProductValue_measurable c)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointBooleanSource (h : D → ℕ) : Measure (JointBlockParameter B h α → ℝ) :=
  sigmaAxisMeasure (fun d => blockCubeMeasure (B d) (Fin (h d)) α)

instance jointBooleanSource_probability (h : D → ℕ) :
    IsProbabilityMeasure (jointBooleanSource (B := B) (α := α) h) := by
  unfold jointBooleanSource
  infer_instance

theorem jointBooleanSampler_image_law (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) :
    Measure.map (jointBooleanSampler h c sets) (jointBooleanSource h) =
      sigmaAxisMeasure (fun d => Measure.map (booleanSamplerMap (F := Fin (h d)) (c d) (sets d))
        (blockCubeMeasure (B d) (Fin (h d)) α)) :=
  sigmaAxisSampler_image_law _ _ (fun d => (booleanSamplerMap_contDiff (c d) (sets d)).continuous.measurable)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]

noncomputable def principalSliceValue (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B × F → ℝ) : ℝ :=
  ∑ b, c b * ∏ k, (lower (b, k) + width (b, k) * x (b, k))

omit [DecidableEq B] [DecidableEq F] in
theorem principalSliceValue_measurable [DecidableEq B] [DecidableEq F]
    (c : B → ℝ) (lower width : B × F → ℝ) :
    Measurable (principalSliceValue c lower width) := by
  unfold principalSliceValue
  fun_prop

def blockCubeShiftScale (lower width : B × F → ℝ)
    (a : BlockParameter B F (Fin 1) → ℝ) (j : BlockParameter B F (Fin 1)) : ℝ :=
  match j.2.2 with
  | none => lower (j.1, j.2.1) + width (j.1, j.2.1) * a j
  | some _ => width (j.1, j.2.1) * a j

omit [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F] in
theorem blockCubeShiftScale_measurable [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]
    (lower width : B × F → ℝ) :
    Measurable (blockCubeShiftScale lower width) := by
  apply Measurable.of_eval
  intro j
  rcases j with ⟨b, k, r⟩
  cases r <;> dsimp only [blockCubeShiftScale] <;> fun_prop

theorem booleanOneCube_shiftScale (c : B → ℝ) (lower width : B × F → ℝ)
    (a : BlockParameter B F (Fin 1) → ℝ) :
    booleanOneCubeEndpoints c (blockCubeShiftScale lower width a) =
      (principalSliceValue c lower width (fun i => a (i.1, i.2, none)),
        principalSliceValue c lower width
          (fun i => a (i.1, i.2, none) + a (i.1, i.2, some 0))) := by
  rw [booleanOneCubeEndpoints_eq]
  simp only [principalProductValue, blockCubeShiftScale, principalSliceValue,
    mul_add, add_assoc]

theorem slicedBooleanOneCube_image (c : B → ℝ) (lower width : B × F → ℝ) :
    ((blockCubeMeasure B F (Fin 1)).map (blockCubeShiftScale lower width)).map
      (booleanOneCubeEndpoints c) =
      ((unitBoxMeasure (B × F)).map (principalSliceValue c lower width)).prod
        ((unitBoxMeasure (B × F)).map (principalSliceValue c lower width)) := by
  rw [blockCubeMeasure,
    Measure.map_map (blockCubeShiftScale_measurable lower width)
      (blockCubeFlatten B F (Fin 1)).continuous.measurable,
    Measure.map_map (booleanOneCubeEndpoints_measurable c)
      ((blockCubeShiftScale_measurable lower width).comp
        (blockCubeFlatten B F (Fin 1)).continuous.measurable)]
  have he : booleanOneCubeEndpoints c ∘
      (blockCubeShiftScale lower width ∘ blockCubeFlatten B F (Fin 1)) =
      (fun a => (principalSliceValue c lower width (fun i => a i none),
        principalSliceValue c lower width (fun i => a i none + a i (some 0)))) := by
    funext a
    rw [Function.comp_apply, Function.comp_apply, booleanOneCube_shiftScale]
    rfl
  rw [he]
  exact scalarOneCube_product_image (B × F) (principalSliceValue c lower width)
    (principalSliceValue_measurable c lower width)

end Erdos3

end

section

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def packPair (x : Fin 2 → (ι → ℝ) × ℝ) : PairInput ι :=
  (((x 0).1, (x 1).1), ((x 0).2, (x 1).2))

theorem packPair_measurePreserving :
    MeasurePreserving (packPair (ι := ι))
      (Measure.pi (fun _ : Fin 2 => (unitBoxMeasure ι).prod unitScalarMeasure))
      (pairSource ι) := by
  have hs := measurePreserving_arrowProdEquivProdArrow (ι → ℝ) ℝ (Fin 2)
    (fun _ => unitBoxMeasure ι) (fun _ => unitScalarMeasure)
  exact ((measurePreserving_finTwoArrow (unitBoxMeasure ι)).prod
    (measurePreserving_finTwoArrow unitScalarMeasure)).comp hs

def packFour (x : Fin 4 → (ι → ℝ) × ℝ) : FourInput ι :=
  (packPair ![x 2, x 3], packPair ![x 0, x 1])

theorem packFour_measurePreserving :
    MeasurePreserving (packFour (ι := ι))
      (Measure.pi (fun _ : Fin 4 => (unitBoxMeasure ι).prod unitScalarMeasure))
      (fourSource ι) := by
  let μ := (unitBoxMeasure ι).prod unitScalarMeasure
  have hr := measurePreserving_piCongrLeft (fun _ : Fin 2 × Fin 2 => μ)
    (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm
  have hc := (finiteArray_uncurry_measurePreserving (fun (_ : Fin 2) (_ : Fin 2) => μ)).symm
    (MeasurableEquiv.curry (Fin 2) (Fin 2) ((ι → ℝ) × ℝ)).symm
  have hp := measurePreserving_pi (fun _ : Fin 2 => Measure.pi (fun _ : Fin 2 => μ))
    (fun _ : Fin 2 => pairSource ι) (fun _ => packPair_measurePreserving (ι := ι))
  have ht := measurePreserving_finTwoArrow (pairSource ι)
  have hw := Measure.measurePreserving_swap (μ := pairSource ι) (ν := pairSource ι)
  exact hw.comp (ht.comp (hp.comp (hc.comp hr)))

def fourBoxPacking (x : Fin 4 × Option ι → ℝ) : FourInput ι :=
  packFour (fun b => ((fun i => x (b, some i)), x (b, none)))

theorem fourBoxPacking_measurePreserving :
    MeasurePreserving (fourBoxPacking (ι := ι))
      (unitBoxMeasure (Fin 4 × Option ι)) (fourSource ι) := by
  have hc := unitBoxMeasure_curry (Fin 4) (Option ι)
  have hp := measurePreserving_pi (fun _ : Fin 4 => unitBoxMeasure (Option ι))
    (fun _ : Fin 4 => (unitBoxMeasure ι).prod unitScalarMeasure)
    (fun _ => unitBoxMeasure_option ι)
  exact packFour_measurePreserving.comp (hp.comp hc)

noncomputable def fourBoxValue (B : Fin 4 → SlicedProductBlock ι)
    (x : Fin 4 × Option ι → ℝ) : ℝ :=
  ∑ b, (B b).value (fun i => x (b, some i)) (x (b, none))

theorem fourBoxValue_eq (B : Fin 4 → SlicedProductBlock ι) (x : Fin 4 × Option ι → ℝ) :
    fourBoxValue B x = fourValue (B 0) (B 1) (B 2) (B 3) (fourBoxPacking x) := by
  simp [fourBoxValue, Fin.sum_univ_four, fourValue, fourBoxPacking, packFour, packPair,
    pairValue, add_assoc]

theorem fourBoxValue_image (B : Fin 4 → SlicedProductBlock ι)
    (hB : ∀ b, (B b).Admissible) :
    (unitBoxMeasure (Fin 4 × Option ι)).map (fourBoxValue B) =
      realDensityMeasure volume (fourDensity (B 0) (B 1) (B 2) (B 3)) := by
  have h := fourSource_image (hB 0) (hB 1) (hB 2) (hB 3)
  rw [← fourBoxPacking_measurePreserving.map_eq,
    Measure.map_map (fourValue_measurable _ _ _ _) fourBoxPacking_measurePreserving.measurable] at h
  simpa only [Function.comp_def, ← fourBoxValue_eq] using h

end Erdos3.SlicedProductBlock

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B ι : Type*} [Fintype B] [Fintype ι] [DecidableEq B] [DecidableEq ι]

def principalSliceBlock (c : B → ℝ) (lower width : B × Option ι → ℝ) (b : B) :
    SlicedProductBlock ι where
  coefficient := c b
  lower i := lower (b, some i)
  width i := width (b, some i)
  lastLower := lower (b, none)
  lastWidth := width (b, none)

omit [DecidableEq B] [DecidableEq ι] in
theorem principalSliceValue_eq_blocks [DecidableEq B] [DecidableEq ι]
    (c : B → ℝ) (lower width : B × Option ι → ℝ)
    (x : B × Option ι → ℝ) :
    principalSliceValue c lower width x =
      ∑ b, (principalSliceBlock c lower width b).value (fun i => x (b, some i)) (x (b, none)) := by
  unfold principalSliceValue SlicedProductBlock.value SlicedProductBlock.prefixProduct
  simp only [Fintype.prod_option, principalSliceBlock]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem principalSliceValue_four_image (c : Fin 4 → ℝ)
    (lower width : Fin 4 × Option ι → ℝ)
    (hB : ∀ b, (principalSliceBlock c lower width b).Admissible) :
    (unitBoxMeasure (Fin 4 × Option ι)).map (principalSliceValue c lower width) =
      realDensityMeasure volume
        (SlicedProductBlock.fourDensity (principalSliceBlock c lower width 0)
          (principalSliceBlock c lower width 1) (principalSliceBlock c lower width 2)
          (principalSliceBlock c lower width 3)) := by
  have he : principalSliceValue c lower width =
      SlicedProductBlock.fourBoxValue (principalSliceBlock c lower width) := by
    funext x
    exact principalSliceValue_eq_blocks c lower width x
  rw [he]
  exact SlicedProductBlock.fourBoxValue_image (principalSliceBlock c lower width) hB

theorem slicedBooleanOneCube_four_density (c : Fin 4 → ℝ)
    (lower width : Fin 4 × Option ι → ℝ)
    (hB : ∀ b, (principalSliceBlock c lower width b).Admissible) :
    ((blockCubeMeasure (Fin 4) (Option ι) (Fin 1)).map (blockCubeShiftScale lower width)).map
      (booleanOneCubeEndpoints c) =
      realDensityMeasure (volume.prod volume)
        (SlicedProductBlock.twoSiteDensity (principalSliceBlock c lower width)) := by
  rw [slicedBooleanOneCube_image, principalSliceValue_four_image c lower width hB]
  have hp := SlicedProductBlock.fourDensity_probability_density (hB 0) (hB 1) (hB 2) (hB 3)
  have hm := (SlicedProductBlock.fourDensity_lipschitz (hB 0) (hB 1) (hB 2) (hB 3)).continuous.measurable
  exact binaryDensity_measure _ _ _ _ hm hm hp.1

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem independentShiftDensity_of_image {T X : Type*}
    [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (z : T → ℝ) (F : X → ℝ) (hz : Measurable z) (hF : Measurable F)
    (f : ℝ → ℝ) (hf : Measurable f) (hfi : Integrable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfmass : (∫ x, f x) = 1)
    (hlaw : ν.map F = realDensityMeasure volume f) :
    (μ.prod ν).map (fun p => F p.2 + z p.1) =
      realDensityMeasure volume (independentShiftDensity μ z f) := by
  apply densityMixture_image_law μ ν volume _
    ((hF.comp measurable_snd).add (hz.comp measurable_fst))
    (fun t x => f (x - z t))
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · intro t
    exact ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hfmass⟩
  · intro t
    have hshift : Measurable (fun u : ℝ => u + z t) := measurable_id.add_const _
    rw [← realDensityMeasure_map_add_right volume f (z t), ← hlaw,
      Measure.map_map hshift hF]
    rfl

variable {J ι : Type*} [Fintype J] [Fintype ι] [DecidableEq J] [DecidableEq ι]

def principalSumBoxSplit (x : (Fin 4 ⊕ J) × Option ι → ℝ) :
    (Fin 4 × Option ι → ℝ) × (J × Option ι → ℝ) :=
  ((fun p => x (.inl p.1, p.2)), (fun p => x (.inr p.1, p.2)))

omit [DecidableEq J] [DecidableEq ι] in
theorem principalSumBoxSplit_measurePreserving [DecidableEq J] [DecidableEq ι] :
    MeasurePreserving (principalSumBoxSplit (J := J) (ι := ι))
      (unitBoxMeasure ((Fin 4 ⊕ J) × Option ι))
      ((unitBoxMeasure (Fin 4 × Option ι)).prod (unitBoxMeasure (J × Option ι))) := by
  exact (unitBoxMeasure_sum (Fin 4 × Option ι) (J × Option ι)).comp
    (unitBoxMeasure_reindex (Equiv.sumProdDistrib (Fin 4) J (Option ι)))

omit [DecidableEq J] [DecidableEq ι] in
theorem principalSliceValue_sum [DecidableEq J] [DecidableEq ι] (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (x : (Fin 4 ⊕ J) × Option ι → ℝ) :
    principalSliceValue c lower width x =
      principalSliceValue (fun b => c (.inl b))
        (fun p => lower (.inl p.1, p.2)) (fun p => width (.inl p.1, p.2))
        (principalSumBoxSplit x).1 +
      principalSliceValue (fun b => c (.inr b))
        (fun p => lower (.inr p.1, p.2)) (fun p => width (.inr p.1, p.2))
        (principalSumBoxSplit x).2 := by
  simp only [principalSliceValue, Fintype.sum_sum_type, principalSumBoxSplit]

noncomputable def principalFourRemainderDensity (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ) : ℝ → ℝ :=
  independentShiftDensity (unitBoxMeasure (J × Option ι))
    (principalSliceValue (fun b => c (.inr b))
      (fun p => lower (.inr p.1, p.2)) (fun p => width (.inr p.1, p.2)))
    (SlicedProductBlock.fourDensity
      (principalSliceBlock c lower width (.inl 0))
      (principalSliceBlock c lower width (.inl 1))
      (principalSliceBlock c lower width (.inl 2))
      (principalSliceBlock c lower width (.inl 3)))

theorem principalSliceValue_extra_image (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (hB : ∀ b : Fin 4, (principalSliceBlock c lower width (.inl b)).Admissible) :
    (unitBoxMeasure ((Fin 4 ⊕ J) × Option ι)).map (principalSliceValue c lower width) =
      realDensityMeasure volume (principalFourRemainderDensity c lower width) := by
  let F := principalSliceValue (fun b => c (.inl b))
    (fun p => lower (.inl p.1, p.2)) (fun p => width (.inl p.1, p.2))
  let z := principalSliceValue (fun b => c (.inr b))
    (fun p => lower (.inr p.1, p.2)) (fun p => width (.inr p.1, p.2))
  let f := SlicedProductBlock.fourDensity
    (principalSliceBlock c lower width (.inl 0))
    (principalSliceBlock c lower width (.inl 1))
    (principalSliceBlock c lower width (.inl 2))
    (principalSliceBlock c lower width (.inl 3))
  have hF : Measurable F := principalSliceValue_measurable _ _ _
  have hz : Measurable z := principalSliceValue_measurable _ _ _
  have hf : Measurable f :=
    (SlicedProductBlock.fourDensity_lipschitz (hB 0) (hB 1) (hB 2) (hB 3)).continuous.measurable
  have hp := SlicedProductBlock.fourDensity_probability_density (hB 0) (hB 1) (hB 2) (hB 3)
  have hlaw : (unitBoxMeasure (Fin 4 × Option ι)).map F = realDensityMeasure volume f :=
    principalSliceValue_four_image _ _ _ hB
  have h := independentShiftDensity_of_image (unitBoxMeasure (J × Option ι))
    (unitBoxMeasure (Fin 4 × Option ι)) z F hz hF f hf hp.2.1 hp.1 hp.2.2 hlaw
  have hs := (Measure.measurePreserving_swap
    (μ := unitBoxMeasure (Fin 4 × Option ι)) (ν := unitBoxMeasure (J × Option ι))).comp
      (principalSumBoxSplit_measurePreserving (J := J) (ι := ι))
  have hm : Measurable (fun p : (J × Option ι → ℝ) × (Fin 4 × Option ι → ℝ) =>
      F p.2 + z p.1) := (hF.comp measurable_snd).add (hz.comp measurable_fst)
  rw [← hs.map_eq, Measure.map_map hm hs.measurable] at h
  have he : (fun p => F p.2 + z p.1) ∘ (Prod.swap ∘ principalSumBoxSplit) =
      principalSliceValue c lower width := by
    funext x
    exact (principalSliceValue_sum c lower width x).symm
  rw [he] at h
  exact h

theorem principalFourRemainderDensity_bounds (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (hB : ∀ b : Fin 4, (principalSliceBlock c lower width (.inl b)).Admissible)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ b : Fin 4, a ≤ |c (.inl b)|)
    (hw : ∀ (b : Fin 4) i, δ ≤ width (.inl b, i)) :
    let K := SlicedProductBlock.uniformCap ι (a * δ ^ (Fintype.card ι + 1))
      (mul_pos ha (pow_pos hδ _))
    (∀ x, principalFourRemainderDensity c lower width x ∈ Set.Icc (0 : ℝ) K) ∧
      LipschitzWith (K * (2 * K)) (principalFourRemainderDensity c lower width) ∧
      Integrable (principalFourRemainderDensity c lower width) ∧
      (∫ x, principalFourRemainderDensity c lower width x) = 1 := by
  dsimp only
  let B := fun b : Fin 4 => principalSliceBlock c lower width (.inl b)
  have hb := SlicedProductBlock.fourDensity_of_uniform_slice_width B hB ha hδ hc
    (fun b => hw b none) (fun b i => hw b (some i))
  have hp := SlicedProductBlock.fourDensity_probability_density (hB 0) (hB 1) (hB 2) (hB 3)
  have hm := hb.2.continuous.measurable
  have hz := principalSliceValue_measurable (fun b => c (.inr b))
    (fun p => lower (.inr p.1, p.2)) (fun p => width (.inr p.1, p.2))
  have hi := independentShiftDensity_probability_density (unitBoxMeasure (J × Option ι))
    hz hm hp.2.1 hp.1 hp.2.2
  refine ⟨independentShiftDensity_cap _ hz hm hb.1, ?_, hi.2.1, hi.2.2⟩
  apply independentShiftDensity_lipschitz _ hz _ hb.2
  intro x
  rw [Real.norm_of_nonneg (hb.1 x).1]
  exact (hb.1 x).2

theorem principalFourRemainderDensity_probability (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (hB : ∀ b : Fin 4, (principalSliceBlock c lower width (.inl b)).Admissible) :
    (∀ x, 0 ≤ principalFourRemainderDensity c lower width x) ∧
      Integrable (principalFourRemainderDensity c lower width) ∧
      (∫ x, principalFourRemainderDensity c lower width x) = 1 := by
  have hp := SlicedProductBlock.fourDensity_probability_density (hB 0) (hB 1) (hB 2) (hB 3)
  exact independentShiftDensity_probability_density _
    (principalSliceValue_measurable _ _ _)
    (SlicedProductBlock.fourDensity_lipschitz (hB 0) (hB 1) (hB 2) (hB 3)).continuous.measurable
    hp.2.1 hp.1 hp.2.2

theorem principalFourRemainderDensity_measurable (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (hB : ∀ b : Fin 4, (principalSliceBlock c lower width (.inl b)).Admissible) :
    Measurable (principalFourRemainderDensity c lower width) :=
  independentShiftDensity_measurable _ (principalSliceValue_measurable _ _ _)
    (SlicedProductBlock.fourDensity_lipschitz (hB 0) (hB 1) (hB 2) (hB 3)).continuous.measurable

theorem slicedBooleanOneCube_extra_density (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (hB : ∀ b : Fin 4, (principalSliceBlock c lower width (.inl b)).Admissible) :
    ((blockCubeMeasure (Fin 4 ⊕ J) (Option ι) (Fin 1)).map
      (blockCubeShiftScale lower width)).map (booleanOneCubeEndpoints c) =
      realDensityMeasure (volume.prod volume)
        (binaryDensity (principalFourRemainderDensity c lower width)
          (principalFourRemainderDensity c lower width)) := by
  rw [slicedBooleanOneCube_image, principalSliceValue_extra_image c lower width hB]
  have hm := principalFourRemainderDensity_measurable c lower width hB
  exact binaryDensity_measure _ _ _ _ hm hm
    (principalFourRemainderDensity_probability c lower width hB).1

theorem slicedOneCube_extra_density_bounds (c : Fin 4 ⊕ J → ℝ)
    (lower width : (Fin 4 ⊕ J) × Option ι → ℝ)
    (hB : ∀ b : Fin 4, (principalSliceBlock c lower width (.inl b)).Admissible)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ b : Fin 4, a ≤ |c (.inl b)|)
    (hw : ∀ (b : Fin 4) i, δ ≤ width (.inl b, i)) :
    let K := SlicedProductBlock.uniformCap ι (a * δ ^ (Fintype.card ι + 1))
      (mul_pos ha (pow_pos hδ _))
    let D := binaryDensity (principalFourRemainderDensity c lower width)
      (principalFourRemainderDensity c lower width)
    (∀ z, D z ∈ Set.Icc (0 : ℝ) (K * K)) ∧
      LipschitzWith (K * (K * (2 * K)) + K * (K * (2 * K))) D := by
  have hb := principalFourRemainderDensity_bounds c lower width hB ha hδ hc hw
  exact ⟨binaryDensity_cap _ _ _ _ hb.1 hb.1,
    binaryDensity_lipschitz _ _ _ _ _ _ hb.1 hb.1 hb.2.1 hb.2.1⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem principalSliceValue_reindex
    {B F B' F' : Type*} [Fintype B] [Fintype F] [Fintype B'] [Fintype F']
    [DecidableEq B] [DecidableEq F] [DecidableEq B'] [DecidableEq F']
    (eB : B' ≃ B) (eF : F' ≃ F) (c : B → ℝ) (lower width : B × F → ℝ)
    (x : B' × F' → ℝ) :
    principalSliceValue c lower width (fun p => x (eB.symm p.1, eF.symm p.2)) =
      principalSliceValue (fun b => c (eB b))
        (fun p => lower (eB p.1, eF p.2)) (fun p => width (eB p.1, eF p.2)) x := by
  unfold principalSliceValue
  rw [← eB.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eB.symm_apply_apply]
  congr 1
  rw [← eF.prod_comp]
  simp only [eF.symm_apply_apply]

theorem principalSliceValue_reindex_image
    {B F B' F' : Type*} [Fintype B] [Fintype F] [Fintype B'] [Fintype F']
    [DecidableEq B] [DecidableEq F] [DecidableEq B'] [DecidableEq F']
    (eB : B' ≃ B) (eF : F' ≃ F) (c : B → ℝ) (lower width : B × F → ℝ) :
    (unitBoxMeasure (B × F)).map (principalSliceValue c lower width) =
      (unitBoxMeasure (B' × F')).map (principalSliceValue (fun b => c (eB b))
        (fun p => lower (eB p.1, eF p.2)) (fun p => width (eB p.1, eF p.2))) := by
  have he := unitBoxMeasure_reindex (eB.prodCongr eF)
  rw [← he.map_eq, Measure.map_map (principalSliceValue_measurable c lower width) he.measurable]
  congr 1
  funext x
  have hr : MeasurableEquiv.piCongrLeft (fun _ : B × F => ℝ) (eB.prodCongr eF) x =
      fun p => x (eB.symm p.1, eF.symm p.2) := by
    funext p
    obtain ⟨b, hb⟩ := eB.surjective p.1
    obtain ⟨f, hf⟩ := eF.surjective p.2
    have hp : p = (eB b, eF f) := Prod.ext hb.symm hf.symm
    rw [hp]
    simpa only [Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map_apply] using
      MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : B × F => ℝ) (eB.prodCongr eF) x (b, f)
  change principalSliceValue c lower width _ = _
  rw [hr]
  exact principalSliceValue_reindex eB eF c lower width x

noncomputable def reindexedSlicedPrincipalDensity
    {B F J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (eB : Fin 4 ⊕ J ≃ B) (eF : Option I ≃ F)
    (c : B → ℝ) (lower width : B × F → ℝ) : ℝ → ℝ :=
  principalFourRemainderDensity (fun b => c (eB b))
    (fun p => lower (eB p.1, eF p.2)) (fun p => width (eB p.1, eF p.2))

theorem reindexedSlicedPrincipalDensity_law_bounds
    {B F J I : Type*} [Fintype B] [Fintype F] [Fintype J] [Fintype I]
    [DecidableEq B] [DecidableEq F] [DecidableEq J] [DecidableEq I]
    (eB : Fin 4 ⊕ J ≃ B) (eF : Option I ≃ F)
    (c : B → ℝ) (lower width : B × F → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ b : Fin 4, a ≤ |c (eB (.inl b))|)
    (hw : ∀ (b : Fin 4) i, δ ≤ width (eB (.inl b), i))
    (hl : ∀ (b : Fin 4) i, 0 ≤ lower (eB (.inl b), i)) :
    let f := reindexedSlicedPrincipalDensity eB eF c lower width
    let K := SlicedProductBlock.uniformCap I (a * δ ^ (Fintype.card I + 1)) (mul_pos ha (pow_pos hδ _))
    (unitBoxMeasure (B × F)).map (principalSliceValue c lower width) = realDensityMeasure volume f ∧
      (∀ x, f x ∈ Set.Icc (0 : ℝ) K) ∧ LipschitzWith (K * (2 * K)) f ∧
        Integrable f ∧ (∫ x, f x) = 1 := by
  have hadm (b : Fin 4) : (principalSliceBlock (fun b => c (eB b))
      (fun p => lower (eB p.1, eF p.2)) (fun p => width (eB p.1, eF p.2)) (.inl b)).Admissible :=
    ⟨abs_pos.mp (ha.trans_le (hc b)), fun i => hl b _, fun i => hδ.trans_le (hw b _), hδ.trans_le (hw b _)⟩
  refine ⟨?_, principalFourRemainderDensity_bounds _ _ _ hadm ha hδ hc (fun b i => hw b (eF i))⟩
  rw [principalSliceValue_reindex_image eB eF]
  exact principalSliceValue_extra_image _ _ _ hadm

noncomputable def fourBlockDecomposition (B : Type*) [Fintype B] (hB : 4 ≤ Fintype.card B) :
    Fin 4 ⊕ Fin (Fintype.card B - 4) ≃ B :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

noncomputable def canonicalSlicedPrincipalDensity
    {B F : Type*} [Fintype B] [Fintype F] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ) (lower width : B × F → ℝ) : ℝ → ℝ :=
  reindexedSlicedPrincipalDensity (fourBlockDecomposition B hB) (Equiv.optionSubtypeNe i) c lower width

theorem canonicalSlicedPrincipalDensity_law_bounds
    {B F : Type*} [Fintype B] [Fintype F] [DecidableEq B] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F) (c : B → ℝ) (lower width : B × F → ℝ)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : ∀ b, a ≤ |c b|) (hw : ∀ p, δ ≤ width p) (hl : ∀ p, 0 ≤ lower p) :
    let f := canonicalSlicedPrincipalDensity hB i c lower width
    let K := SlicedProductBlock.uniformCap {j : F // j ≠ i}
      (a * δ ^ (Fintype.card {j : F // j ≠ i} + 1)) (mul_pos ha (pow_pos hδ _))
    (unitBoxMeasure (B × F)).map (principalSliceValue c lower width) = realDensityMeasure volume f ∧
      (∀ x, f x ∈ Set.Icc (0 : ℝ) K) ∧ LipschitzWith (K * (2 * K)) f ∧
        Integrable f ∧ (∫ x, f x) = 1 :=
  reindexedSlicedPrincipalDensity_law_bounds (fourBlockDecomposition B hB) (Equiv.optionSubtypeNe i)
    c lower width ha hδ (fun _ => hc _) (fun _ _ => hw _) (fun _ _ => hl _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem independentShiftDensity_measurable_family
    {P T : Type*} [MeasurableSpace P] [MeasurableSpace T]
    (μ : Measure T) [SFinite μ] (z : P → T → ℝ) (f : P → ℝ → ℝ)
    (hz : Measurable (Function.uncurry z)) (hf : Measurable (Function.uncurry f)) :
    Measurable (fun p : P × ℝ => independentShiftDensity μ (z p.1) (f p.1) p.2) := by
  have hz' : Measurable (fun q : (P × ℝ) × T => z q.1.1 q.2) :=
    hz.comp (measurable_fst.fst.prodMk measurable_snd)
  have hm : Measurable (fun q : (P × ℝ) × T => f q.1.1 (q.1.2 - z q.1.1 q.2)) :=
    hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.sub hz'))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem principalFourRemainderDensity_measurable_family
    {P J I : Type*} [MeasurableSpace P] [Fintype J] [Fintype I]
    [DecidableEq J] [DecidableEq I]
    (c : P → Fin 4 ⊕ J → ℝ) (lower width : P → (Fin 4 ⊕ J) × Option I → ℝ)
    (hc : ∀ b, Measurable (fun p => c p b))
    (hl : ∀ j, Measurable (fun p => lower p j)) (hw : ∀ j, Measurable (fun p => width p j)) :
    Measurable (fun p : P × ℝ => principalFourRemainderDensity (c p.1) (lower p.1) (width p.1) p.2) := by
  have hblock (b : Fin 4) : SlicedProductBlock.MeasurableFamily
      (fun p => principalSliceBlock (c p) (lower p) (width p) (.inl b)) :=
    ⟨hc (.inl b), fun i => hl (.inl b, some i), fun i => hw (.inl b, some i),
      hl (.inl b, none), hw (.inl b, none)⟩
  have hz : Measurable (fun p : P × (J × Option I → ℝ) =>
      principalSliceValue (fun b => c p.1 (.inr b))
        (fun j => lower p.1 (.inr j.1, j.2)) (fun j => width p.1 (.inr j.1, j.2)) p.2) := by
    unfold principalSliceValue
    fun_prop
  have hf := SlicedProductBlock.fourDensity_measurable_family (hblock 0) (hblock 1) (hblock 2) (hblock 3)
  have he := independentShiftDensity_measurable_family (unitBoxMeasure (J × Option I))
    (fun p => principalSliceValue (fun b => c p (.inr b))
      (fun j => lower p (.inr j.1, j.2)) (fun j => width p (.inr j.1, j.2)))
    (fun p => SlicedProductBlock.fourDensity
      (principalSliceBlock (c p) (lower p) (width p) (.inl 0))
      (principalSliceBlock (c p) (lower p) (width p) (.inl 1))
      (principalSliceBlock (c p) (lower p) (width p) (.inl 2))
      (principalSliceBlock (c p) (lower p) (width p) (.inl 3))) hz hf
  exact he

theorem canonicalSlicedPrincipalDensity_measurable_family
    {P B F : Type*} [MeasurableSpace P] [Fintype B] [Fintype F] [DecidableEq F]
    (hB : 4 ≤ Fintype.card B) (i : F)
    (c : P → B → ℝ) (lower width : P → B × F → ℝ)
    (hc : ∀ b, Measurable (fun p => c p b))
    (hl : ∀ j, Measurable (fun p => lower p j)) (hw : ∀ j, Measurable (fun p => width p j)) :
    Measurable (fun p : P × ℝ => canonicalSlicedPrincipalDensity hB i (c p.1) (lower p.1) (width p.1) p.2) :=
  principalFourRemainderDensity_measurable_family
    (fun p b => c p (fourBlockDecomposition B hB b))
    (fun p j => lower p (fourBlockDecomposition B hB j.1, Equiv.optionSubtypeNe i j.2))
    (fun p j => width p (fourBlockDecomposition B hB j.1, Equiv.optionSubtypeNe i j.2))
    (fun _ => hc _) (fun _ => hl _) (fun _ => hw _)

end Erdos3

end

end OAI
