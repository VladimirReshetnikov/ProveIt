/-
Modified for ProveIt: construct mapped probability-measure instances from
the existing measurability proofs on Lean 4.32. All upstream statements and
quantitative bounds are unchanged.
-/
import OAI.Combinatorics.Progressions.Geometry.FixedSpatialEmptyCoordinates
import OAI.Combinatorics.Progressions.Linear.FixedSpatialKernelSliceDensity
import OAI.Combinatorics.Progressions.Sampling.ForecastOriginalSampleUniformBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X]
  [MeasurableSpace T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Input" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a)) (fun a : Active => degree (Subtype.val a))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Domain" => ((X → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (μ : Measure T) [IsProbabilityMeasure μ] (center : X → ℝ) {rest : T → X → ℝ}
variable (hrest : Measurable rest) (A₁ A₂ : (X → ℝ) ≃L[ℝ] (X → ℝ))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def fixedSpatialOriginalSampleForecastDensity (sample : Sample) : Domain → ℝ :=
  binaryDensity (fixedSpatialBlockDensity μ center rest A₁ A₂)
    (allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample))

noncomputable def fixedSpatialOriginalSampleForecastSource (sample : Sample) : Measure Domain :=
  (realDensityMeasure volume (fixedSpatialBlockDensity μ center rest A₁ A₂)).prod
    ((unitBoxMeasure Input).map (allocatedOriginalSampleLiftMap B U basis S lower width sample))

noncomputable def fixedSpatialOriginalForecastCap {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  fixedSpatialBlockDensityCap A₂ * allocatedForecastAllAxisLiftCap B hδ

noncomputable def fixedSpatialOriginalForecastLip {δ : ℝ} (hδ : 0 < δ) : ℝ≥0 :=
  allocatedForecastAllAxisLiftCap B hδ * fixedSpatialBlockDensityLipschitz A₁ A₂ +
    fixedSpatialBlockDensityCap A₂ * allocatedForecastAllAxisLiftLip B hδ

local notation "spatial" => fixedSpatialBlockDensity μ center rest A₁ A₂
local notation "liftDensity" => (fun sample => allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample))
local notation "density" => fixedSpatialOriginalSampleForecastDensity (rest := rest)
  B U basis S μ center A₁ A₂ hB lower width
local notation "source" => fixedSpatialOriginalSampleForecastSource (rest := rest)
  B U basis S μ center A₁ A₂ lower width

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hrest hδ hw hl hs in
theorem fixedSpatialOriginalSampleForecastDensity_probability_data :
    (∀ y, 0 ≤ density sample y) ∧ Integrable (density sample) ∧
      (∫ y, density sample y) = 1 := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hf := fixedSpatialBlockDensity_probability_density μ center hrest A₁ A₂
  have hg := allocatedFixedPathLiftDensity_law_probability B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  refine ⟨fun y => mul_nonneg (hf.1 y.1) (hg.2.1 y.2),
    binaryDensity_integrable hf.2.1 hg.2.2.1, ?_⟩
  change (∫ y, binaryDensity spatial (liftDensity sample) y ∂volume.prod volume) = 1
  rw [binaryDensity_mass, hf.2.2, hg.2.2.2, one_mul]

include hR hσ hrest hδ hw hl hs in
theorem fixedSpatialOriginalSampleForecastDensity_bounds :
    (∀ y, density sample y ∈ Set.Icc (0 : ℝ) (fixedSpatialOriginalForecastCap B A₂ hδ)) ∧
      LipschitzWith (fixedSpatialOriginalForecastLip B A₁ A₂ hδ) (density sample) := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hf := fixedSpatialBlockDensity_bounds μ center hrest A₁ A₂
  have hg := allocatedFixedPathLiftDensity_cap_lipschitz B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  have hgcap : ∀ y, liftDensity sample y ∈ Set.Icc (0 : ℝ) (allocatedForecastAllAxisLiftCap B hδ) := by
    intro y
    exact ⟨(hg.1 y).1, (hg.1 y).2.trans (by
      exact_mod_cast allocatedFixedPathLift_prod_le_allAxis B short hδ)⟩
  have hglip := hg.2.weaken (allocatedFixedPathLift_lip_le_allAxis B short hδ)
  exact ⟨binaryDensity_cap spatial (liftDensity sample) _ _ hf.1 hgcap,
    binaryDensity_lipschitz spatial (liftDensity sample) _ _ _ _ hf.1 hgcap hf.2 hglip⟩

include hR hσ hrest hδ hw hl hs in
theorem fixedSpatialOriginalSampleForecastSource_density :
    source sample = realDensityMeasure volume (density sample) := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hg := allocatedFixedPathLiftDensity_law_probability B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  have hglip := allocatedFixedPathLiftDensity_cap_lipschitz B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  unfold fixedSpatialOriginalSampleForecastSource
  rw [allocatedOriginalSampleLiftMap_eq_fixedPath B U basis S lower width hR hσ sample, hg.1]
  exact binaryDensity_measure volume volume spatial (liftDensity sample)
    (fixedSpatialBlockDensity_measurable μ center hrest A₁ A₂) hglip.2.continuous.measurable
    (fun y => (fixedSpatialBlockDensity_bounds μ center hrest A₁ A₂).1 y |>.1)

include hrest in
theorem fixedSpatialOriginalSampleForecastSource_probability :
    IsProbabilityMeasure (source sample) := by
  let := fixedSpatialBlockDensity_probability μ center hrest A₁ A₂
  let : IsProbabilityMeasure ((unitBoxMeasure Input).map
      (allocatedOriginalSampleLiftMap B U basis S lower width sample)) :=
    Measure.isProbabilityMeasure_map
      (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample).aemeasurable
  change IsProbabilityMeasure ((realDensityMeasure volume spatial).prod _)
  infer_instance

include hrest in
theorem fixedSpatialOriginalSampleForecastSource_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C) :
    (∫ y, φ y ∂source sample) =
      ∫ z, ∫ v, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample v)
        ∂unitBoxMeasure Input ∂realDensityMeasure volume spatial := by
  let := fixedSpatialBlockDensity_probability μ center hrest A₁ A₂
  exact probability_prod_map_integral (realDensityMeasure volume spatial) (unitBoxMeasure Input)
    (allocatedOriginalSampleLiftMap B U basis S lower width sample)
    (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample) φ hφ hC

include hR hσ hrest hδ hw hl hs in
theorem fixedSpatialOriginalSampleForecastDensity_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C) :
    (∫ y, φ y ∂realDensityMeasure volume (density sample)) =
      ∫ z, ∫ v, φ (z, allocatedOriginalSampleLiftMap B U basis S lower width sample v)
        ∂unitBoxMeasure Input ∂realDensityMeasure volume spatial := by
  rw [← fixedSpatialOriginalSampleForecastSource_density B U basis hR hσ S μ center hrest
    A₁ A₂ hB lower width hδ hw hl sample hs]
  exact fixedSpatialOriginalSampleForecastSource_test_integral B U basis S μ center hrest
    A₁ A₂ lower width sample φ hφ hC

include hrest in
theorem fixedSpatialOriginalSampleForecastSource_image :
    ((μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))).prod
      (unitBoxMeasure Input)).map
      (fun p => (center + A₁ p.1.2.1 + A₂ p.1.2.2 + rest p.1.1,
        allocatedOriginalSampleLiftMap B U basis S lower width sample p.2)) =
      source sample := by
  unfold fixedSpatialOriginalSampleForecastSource
  rw [← fixedSpatialBlockDensity_image_law μ center hrest A₁ A₂]
  have hmap : Measurable (fun p : T × ((X → ℝ) × (X → ℝ)) =>
      center + A₁ p.2.1 + A₂ p.2.2 + rest p.1) := by fun_prop
  exact (Measure.map_prod_map _ _ hmap
    (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample)).symm

include hR hσ hrest hδ hw hl hs in
theorem fixedSpatialOriginalSampleForecastDensity_image :
    ((μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))).prod
      (unitBoxMeasure Input)).map
      (fun p => (center + A₁ p.1.2.1 + A₂ p.1.2.2 + rest p.1.1,
        allocatedOriginalSampleLiftMap B U basis S lower width sample p.2)) =
      realDensityMeasure volume (density sample) := by
  rw [fixedSpatialOriginalSampleForecastSource_image B U basis S μ center hrest A₁ A₂
    lower width sample]
  exact fixedSpatialOriginalSampleForecastSource_density B U basis hR hσ S μ center hrest
    A₁ A₂ hB lower width hδ hw hl sample hs

include hR hσ hrest hδ hw hl hs in
theorem fixedSpatialOriginalSampleForecastDensity_product_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) :
    (∫ y, φ y ∂realDensityMeasure volume (density sample)) =
      ∫ p, φ (center + A₁ p.1.2.1 + A₂ p.1.2.2 + rest p.1.1,
        allocatedOriginalSampleLiftMap B U basis S lower width sample p.2)
        ∂((μ.prod ((unitBoxMeasure X).prod (unitBoxMeasure X))).prod
          (unitBoxMeasure Input)) := by
  rw [← fixedSpatialOriginalSampleForecastDensity_image B U basis hR hσ S μ center hrest
    A₁ A₂ hB lower width hδ hw hl sample hs]
  apply integral_map _ hφ.aestronglyMeasurable
  exact (Measurable.prodMk (by fun_prop)
    ((allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample).comp
      measurable_snd)).aemeasurable

noncomputable def fixedSpatialOriginalSampleNormalizedForecast (y : Domain) : ℂ :=
  (density sample y : ℂ) / (((fixedSpatialOriginalForecastCap B A₂ hδ : ℝ) + 1 : ℝ) : ℂ)

include hR hσ hrest hw hl hs in
theorem fixedSpatialOriginalSampleNormalizedForecast_bounds :
    let F := fixedSpatialOriginalSampleNormalizedForecast (rest := rest)
      B U basis S μ center A₁ A₂ hB lower width hδ sample
    (∀ y, ‖F y‖ ≤ 1) ∧
      LipschitzWith (fixedSpatialOriginalForecastLip B A₁ A₂ hδ) F ∧
      (∀ y, (density sample y : ℂ) =
        (((fixedSpatialOriginalForecastCap B A₂ hδ : ℝ) + 1 : ℝ) : ℂ) * F y) := by
  intro F
  have hb := fixedSpatialOriginalSampleForecastDensity_bounds B U basis hR hσ S μ center hrest
    A₁ A₂ hB lower width hδ hw hl sample hs
  let cap := fixedSpatialOriginalForecastCap B A₂ hδ
  have hpos : (0 : ℝ) < cap + 1 := by positivity
  have hden : ‖(((cap : ℝ) + 1 : ℝ) : ℂ)‖ = (cap : ℝ) + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    change ‖(density sample y : ℂ) / (((cap : ℝ) + 1 : ℝ) : ℂ)‖ ≤ 1
    rw [norm_div, hden, Complex.norm_real, Real.norm_of_nonneg (hb.1 y).1]
    exact (div_le_one hpos).mpr ((hb.1 y).2.trans (le_add_of_nonneg_right zero_le_one))
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((density sample x : ℂ) / (((cap : ℝ) + 1 : ℝ) : ℂ))
      ((density sample y : ℂ) / (((cap : ℝ) + 1 : ℝ) : ℂ)) ≤ _
    rw [dist_eq_norm, ← sub_div, norm_div, ← Complex.ofReal_sub, Complex.norm_real, hden]
    exact (div_le_self (norm_nonneg _) (le_add_of_nonneg_left cap.coe_nonneg)).trans
      (by simpa only [dist_eq_norm] using hb.2.dist_le_mul x y)
  · intro y
    change (density sample y : ℂ) = (((cap : ℝ) + 1 : ℝ) : ℂ) *
      ((density sample y : ℂ) / (((cap : ℝ) + 1 : ℝ) : ℂ))
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

theorem fixedSpatialOriginalForecast_uniform_budget
    {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {X : Type*} [Fintype X]
    (A₀ A₁ : (X → ℝ) ≃L[ℝ] (X → ℝ))
    {P δ : ℝ} (hP : 1 ≤ P) (hδ : 0 < δ)
    (hδinv : δ⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (hjac : inverseJacobian A₁ ≤ Real.exp P)
    (hinverse : ‖A₀.symm.toContinuousLinearMap‖ ≤ Real.exp P) :
    (fixedSpatialOriginalForecastCap B A₁ hδ : ℝ) + 1 ≤
        Real.exp (forecastOriginalSmoothBudget m P) ∧
      (fixedSpatialOriginalForecastLip B A₀ A₁ hδ : ℝ) ≤
        Real.exp (forecastOriginalSmoothBudget m P) := by
  let Q := ((m : ℝ) + 2) * P + 4 * m + 8
  let E := P * (Q + 1)
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hlift := allocatedForecastAllAxisLift_budget B hP hδ hδinv haxes hblocks
  have hspCap : (fixedSpatialBlockDensityCap A₁ : ℝ) ≤ Real.exp P := by
    rw [fixedSpatialBlockDensityCap_eq]
    exact hjac
  have hJ0 : 0 ≤ inverseJacobian A₁ := by
    rw [← fixedSpatialBlockDensityCap_eq]
    positivity
  have hcount : (Fintype.card X : ℝ) ≤ Real.exp P :=
    hX.trans (by linarith [Real.add_one_le_exp P])
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hspLip : (fixedSpatialBlockDensityLipschitz A₀ A₁ : ℝ) ≤ Real.exp (3 * P + 1) := by
    rw [fixedSpatialBlockDensityLipschitz_eq]
    calc
      _ ≤ Real.exp 1 * Real.exp P * Real.exp P * Real.exp P := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hcap : (fixedSpatialOriginalForecastCap B A₁ hδ : ℝ) ≤ Real.exp (P + E) := by
    rw [fixedSpatialOriginalForecastCap, NNReal.coe_mul]
    exact (mul_le_mul hspCap hlift.1 (by positivity) (Real.exp_nonneg _)).trans_eq
      (Real.exp_add _ _).symm
  have hfirst : (allocatedForecastAllAxisLiftCap B hδ : ℝ) *
      fixedSpatialBlockDensityLipschitz A₀ A₁ ≤ Real.exp (E + 3 * P + 1) := by
    calc
      _ ≤ Real.exp E * Real.exp (3 * P + 1) :=
        mul_le_mul hlift.1 hspLip (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsecond : (fixedSpatialBlockDensityCap A₁ : ℝ) *
      allocatedForecastAllAxisLiftLip B hδ ≤ Real.exp (E + 2 * P + 2 * Q + 1) := by
    calc
      _ ≤ Real.exp P * Real.exp (E + P + 2 * Q + 1) :=
        mul_le_mul hspCap hlift.2 (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlip : (fixedSpatialOriginalForecastLip B A₀ A₁ hδ : ℝ) ≤
      Real.exp (2 * E + 5 * P + 2 * Q + 3) := by
    have hh := add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond
    rw [fixedSpatialOriginalForecastLip, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mul]
    convert hh using 1
    congr 1
    ring
  have hbudget := forecastOriginalSmoothBudget_bounds m hP0
  have hcapBudget : P + E + 1 ≤ forecastOriginalSmoothBudget m P := by
    apply le_trans _ hbudget.2.1
    change P + E + 1 ≤ P * (2 * P + 1) + E + 1
    nlinarith [sq_nonneg P]
  have hlipBudget : 2 * E + 5 * P + 2 * Q + 3 ≤ forecastOriginalSmoothBudget m P := by
    apply le_trans _ hbudget.2.2
    change 2 * E + 5 * P + 2 * Q + 3 ≤
      2 * P * (2 * P + 1) + 2 * P * (Q + 1) + 2 * P + (4 * P + 2) + 2 * Q + 2
    dsimp only [E]
    nlinarith [sq_nonneg P]
  constructor
  · have hh := one_add_le_exp_succ (add_nonneg hP0 hE) hcap
    rw [add_comm 1] at hh
    exact hh.trans (Real.exp_le_exp.mpr hcapBudget)
  · exact hlip.trans (Real.exp_le_exp.mpr hlipBudget)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def fixedSpatialKernelOriginalForecastDensity (sample : Sample) : Domain → ℝ :=
  binaryDensity (fixedSpatialEmptyDensity (fixedSpatialKernelDensity e W L z h0 h1))
    (allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample))

noncomputable def fixedSpatialKernelOriginalForecastSource (sample : Sample) : Measure Domain :=
  ((unitBoxMeasure G).prod (unitBoxMeasure Input)).map
    (fun p => (fixedSpatialKernelMap W L z p.1,
      allocatedOriginalSampleLiftMap B U basis S lower width sample p.2))

local notation "A₀" => fixedSpatialKernelBlockEquiv e W L z false h0
local notation "A₁" => fixedSpatialKernelBlockEquiv e W L z true h1
local notation "spatial" => fixedSpatialEmptyDensity (fixedSpatialKernelDensity e W L z h0 h1)
local notation "liftDensity" => (fun sample => allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample))
local notation "density" => fixedSpatialKernelOriginalForecastDensity B U basis S e W L z h0 h1 hB lower width
local notation "source" => fixedSpatialKernelOriginalForecastSource B U basis S W L z lower width

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

omit hR hσ [Fintype X] [DecidableEq X] in
theorem fixedSpatialKernelMap_measurable : Measurable (fixedSpatialKernelMap W L z) := by
  unfold fixedSpatialKernelMap
  fun_prop

omit hR hσ in
theorem fixedSpatialKernelEmptyDensity_image_law :
    (unitBoxMeasure G).map (fixedSpatialKernelMap W L z) = realDensityMeasure volume spatial := by
  have he : fixedSpatialKernelMap W L z =
      fixedSpatialEmptyCoordinates ∘ (fun t x => fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩) := rfl
  have hm : Measurable (fun t : G → ℝ => fun x : X =>
      fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩) :=
    by unfold fixedSpatialKernelMap; fun_prop
  rw [he, ← Measure.map_map fixedSpatialEmptyCoordinates.continuous.measurable hm]
  rw [fixedSpatialKernelDensity_image_law e W L z h0 h1, fixedSpatialEmptyDensity_image_law]

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastSource_density :
    source sample = realDensityMeasure volume (density sample) := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hg := allocatedFixedPathLiftDensity_law_probability B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  have hglip := allocatedFixedPathLiftDensity_cap_lipschitz B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  have hf := fixedSpatialKernelDensity_bounds e W L z h0 h1
  have hf' := fixedSpatialEmptyDensity_bounds _ hf.1 hf.2
  unfold fixedSpatialKernelOriginalForecastSource
  change Measure.map (Prod.map (fixedSpatialKernelMap W L z)
    (allocatedOriginalSampleLiftMap B U basis S lower width sample))
    ((unitBoxMeasure G).prod (unitBoxMeasure Input)) = _
  rw [← Measure.map_prod_map _ _ (fixedSpatialKernelMap_measurable W L z)
    (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample)]
  rw [fixedSpatialKernelEmptyDensity_image_law e W L z h0 h1,
    allocatedOriginalSampleLiftMap_eq_fixedPath B U basis S lower width hR hσ sample, hg.1]
  exact binaryDensity_measure volume volume spatial (liftDensity sample)
    hf'.2.continuous.measurable hglip.2.continuous.measurable (fun y => (hf'.1 y).1)

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_probability_data :
    (∀ y, 0 ≤ density sample y) ∧ Integrable (density sample) ∧
      (∫ y, density sample y) = 1 := by
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hf := fixedSpatialKernelDensity_probability_density e W L z h0 h1
  have hf' := fixedSpatialEmptyDensity_probability_data _ hf.1 hf.2.1 hf.2.2
  have hg := allocatedFixedPathLiftDensity_law_probability B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  refine ⟨fun y => mul_nonneg (hf'.1 y.1) (hg.2.1 y.2),
    binaryDensity_integrable hf'.2.1 hg.2.2.1, ?_⟩
  change (∫ y, binaryDensity spatial (liftDensity sample) y ∂volume.prod volume) = 1
  rw [binaryDensity_mass, hf'.2.2, hg.2.2.2, one_mul]

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_bounds :
    (∀ y, density sample y ∈ Set.Icc (0 : ℝ) (fixedSpatialOriginalForecastCap B A₁ hδ)) ∧
      LipschitzWith (fixedSpatialOriginalForecastLip B A₀ A₁ hδ) (density sample) := by
  have hf := fixedSpatialKernelDensity_bounds e W L z h0 h1
  have hf' := fixedSpatialEmptyDensity_bounds _ hf.1 hf.2
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hg := allocatedFixedPathLiftDensity_cap_lipschitz B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  have hgcap : ∀ y, liftDensity sample y ∈ Set.Icc (0 : ℝ) (allocatedForecastAllAxisLiftCap B hδ) := by
    intro y
    exact ⟨(hg.1 y).1, (hg.1 y).2.trans (by
      exact_mod_cast allocatedFixedPathLift_prod_le_allAxis B short hδ)⟩
  have hglip := hg.2.weaken (allocatedFixedPathLift_lip_le_allAxis B short hδ)
  exact ⟨binaryDensity_cap spatial (liftDensity sample) _ _ hf'.1 hgcap,
    binaryDensity_lipschitz spatial (liftDensity sample) _ _ _ _ hf'.1 hgcap hf'.2 hglip⟩

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_bounds_of_det
    {H κ0 κ1 : ℝ} (hH : 0 ≤ H) (hκ0 : 0 < κ0) (hκ1 : 0 < κ1)
    (hentry : ∀ i j, |fixedSpatialKernelBlock e W L z false i j| ≤ H)
    (hdet0 : κ0 ≤ |(fixedSpatialKernelBlock e W L z false).det|)
    (hdet1 : κ1 ≤ |(fixedSpatialKernelBlock e W L z true).det|) :
    let Csp : ℝ≥0 := Real.toNNReal (κ1⁻¹)
    let Ksp : ℝ≥0 := 2 * (Fintype.card X : ℝ≥0) * Csp *
      Real.toNNReal (Fintype.card X * ((Fintype.card X).factorial *
        H ^ (Fintype.card X - 1) / κ0))
    (∀ y, density sample y ∈ Set.Icc (0 : ℝ)
      (Csp * allocatedForecastAllAxisLiftCap B hδ)) ∧
    LipschitzWith (allocatedForecastAllAxisLiftCap B hδ * Ksp +
      Csp * allocatedForecastAllAxisLiftLip B hδ) (density sample) := by
  intro Csp Ksp
  have hf := fixedSpatialKernelDensity_bounds_of_det e W L z h0 h1
    hH hκ0 hκ1 hentry hdet0 hdet1
  have hfcap : ∀ x, fixedSpatialKernelDensity e W L z h0 h1 x ∈ Set.Icc (0 : ℝ) Csp := by
    simpa only [Csp, Real.coe_toNNReal _ (inv_nonneg.mpr hκ1.le)] using hf.1
  have hf' := fixedSpatialEmptyDensity_bounds _ hfcap hf.2
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hg := allocatedFixedPathLiftDensity_cap_lipschitz B short R σ
    (fun j => (hR j).ne') hB lower width hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr
  have hgcap : ∀ y, liftDensity sample y ∈ Set.Icc (0 : ℝ) (allocatedForecastAllAxisLiftCap B hδ) := by
    intro y
    exact ⟨(hg.1 y).1, (hg.1 y).2.trans (by
      exact_mod_cast allocatedFixedPathLift_prod_le_allAxis B short hδ)⟩
  have hglip := hg.2.weaken (allocatedFixedPathLift_lip_le_allAxis B short hδ)
  exact ⟨binaryDensity_cap spatial (liftDensity sample) _ _ hf'.1 hgcap,
    binaryDensity_lipschitz spatial (liftDensity sample) _ _ _ _ hf'.1 hgcap hf'.2 hglip⟩

omit hR hσ [Fintype X] [DecidableEq X] in
theorem fixedSpatialKernelOriginalForecastSource_probability :
    IsProbabilityMeasure (source sample) := by
  unfold fixedSpatialKernelOriginalForecastSource
  exact Measure.isProbabilityMeasure_map
    (((fixedSpatialKernelMap_measurable W L z).comp measurable_fst).prodMk
      ((allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample).comp
        measurable_snd)).aemeasurable

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) :
    (∫ y, φ y ∂realDensityMeasure volume (density sample)) =
      ∫ p, φ (fixedSpatialKernelMap W L z p.1,
        allocatedOriginalSampleLiftMap B U basis S lower width sample p.2)
        ∂(unitBoxMeasure G).prod (unitBoxMeasure Input) := by
  rw [← fixedSpatialKernelOriginalForecastSource_density B U basis hR hσ S e W L z h0 h1
    hB lower width hδ hw hl sample hs]
  apply integral_map _ hφ.aestronglyMeasurable
  exact (((fixedSpatialKernelMap_measurable W L z).comp measurable_fst).prodMk
    ((allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample).comp
      measurable_snd)).aemeasurable

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

theorem fixedSpatialKernelOriginalForecastDensity_iterated_test_integral
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
    (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
    (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
    (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (φ : Domain → ℂ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    (∫ y, φ y ∂realDensityMeasure volume
      (fixedSpatialKernelOriginalForecastDensity B U basis S e W L z h0 h1 hB lower width sample)) =
      ∫ k, ∫ v, φ (fixedSpatialKernelMap W L z k,
        allocatedOriginalSampleLiftMap B U basis S lower width sample v)
        ∂unitBoxMeasure Input ∂unitBoxMeasure G := by
  rw [fixedSpatialKernelOriginalForecastDensity_test_integral B U basis hR hσ S
    e W L z h0 h1 hB lower width hδ hw hl sample hs φ hφ]
  apply integral_prod
  refine ⟨?_, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun p => hbound _))⟩
  exact (hφ.comp (((fixedSpatialKernelMap_measurable W L z).comp measurable_fst).prodMk
    ((allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lower width sample).comp
      measurable_snd))).aestronglyMeasurable

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "A₀" => fixedSpatialKernelBlockEquiv e W L z false h0
local notation "A₁" => fixedSpatialKernelBlockEquiv e W L z true h1
local notation "density" => fixedSpatialKernelOriginalForecastDensity B U basis S e W L z h0 h1 hB lower width

variable {δ : ℝ} (hδ : 0 < δ)

noncomputable def fixedSpatialKernelOriginalNormalizedForecast
    (sample : Sample) (y : Domain) : ℂ :=
  (density sample y : ℂ) / (((fixedSpatialOriginalForecastCap B A₁ hδ : ℝ) + 1 : ℝ) : ℂ)

variable (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

local notation "normalized" => fixedSpatialKernelOriginalNormalizedForecast
  B U basis S e W L z h0 h1 hB lower width hδ sample

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalNormalizedForecast_bounds :
    (∀ y, ‖normalized y‖ ≤ 1) ∧
      LipschitzWith (fixedSpatialOriginalForecastLip B A₀ A₁ hδ) normalized ∧
      (∀ y, (density sample y : ℂ) =
        (((fixedSpatialOriginalForecastCap B A₁ hδ : ℝ) + 1 : ℝ) : ℂ) * normalized y) := by
  have hb := fixedSpatialKernelOriginalForecastDensity_bounds B U basis hR hσ S e W L z h0 h1
    hB lower width hδ hw hl sample hs
  let cap := fixedSpatialOriginalForecastCap B A₁ hδ
  have hpos : (0 : ℝ) < cap + 1 := by positivity
  have hden : ‖(((cap : ℝ) + 1 : ℝ) : ℂ)‖ = (cap : ℝ) + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hpos.le]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    change ‖(density sample y : ℂ) / (((cap : ℝ) + 1 : ℝ) : ℂ)‖ ≤ 1
    rw [norm_div, hden, Complex.norm_real, Real.norm_of_nonneg (hb.1 y).1]
    exact (div_le_one hpos).mpr ((hb.1 y).2.trans (le_add_of_nonneg_right zero_le_one))
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist ((density sample x : ℂ) / (((cap : ℝ) + 1 : ℝ) : ℂ))
      ((density sample y : ℂ) / (((cap : ℝ) + 1 : ℝ) : ℂ)) ≤ _
    rw [dist_eq_norm, ← sub_div, norm_div, ← Complex.ofReal_sub, Complex.norm_real, hden]
    exact (div_le_self (norm_nonneg _) (le_add_of_nonneg_left cap.coe_nonneg)).trans
      (by simpa only [dist_eq_norm] using hb.2.dist_le_mul x y)
  · intro y
    change (density sample y : ℂ) = (((cap : ℝ) + 1 : ℝ) : ℂ) *
      ((density sample y : ℂ) / (((cap : ℝ) + 1 : ℝ) : ℂ))
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hpos.ne')]

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_weighted_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) :
    (∫ y, (density sample y : ℂ) * φ y) =
      ∫ p, φ (fixedSpatialKernelMap W L z p.1,
        allocatedOriginalSampleLiftMap B U basis S lower width sample p.2)
        ∂(unitBoxMeasure G).prod (unitBoxMeasure Input) := by
  have hb := fixedSpatialKernelOriginalForecastDensity_bounds B U basis hR hσ S e W L z h0 h1
    hB lower width hδ hw hl sample hs
  rw [← realDensityMeasure_integral_complex volume (density sample)
    hb.2.continuous.measurable (fun y => (hb.1 y).1) φ]
  exact fixedSpatialKernelOriginalForecastDensity_test_integral B U basis hR hσ S e W L z h0 h1
    hB lower width hδ hw hl sample hs φ hφ

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalNormalizedForecast_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) :
    (((fixedSpatialOriginalForecastCap B A₁ hδ : ℝ) + 1 : ℝ) : ℂ) *
      (∫ y, normalized y * φ y) =
      ∫ p, φ (fixedSpatialKernelMap W L z p.1,
        allocatedOriginalSampleLiftMap B U basis S lower width sample p.2)
        ∂(unitBoxMeasure G).prod (unitBoxMeasure Input) := by
  have hb := fixedSpatialKernelOriginalNormalizedForecast_bounds B U basis hR hσ S e W L z h0 h1
    hB lower width hδ hw hl sample hs
  rw [← integral_const_mul]
  calc
    _ = ∫ y, (density sample y : ℂ) * φ y := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only
        rw [← mul_assoc, ← hb.2.2 y])
    _ = _ := fixedSpatialKernelOriginalForecastDensity_weighted_test_integral
      B U basis hR hσ S e W L z h0 h1 hB lower width hδ hw hl sample hs φ hφ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [DecidableEq X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "density" => fixedSpatialKernelOriginalForecastDensity B U basis S e W L z h0 h1 hB lower width

variable {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_zero_of_active_norm_gt_two
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (y : Domain) (hy : 2 < ‖y.2‖) : density sample y = 0 := by
  classical
  have hr := allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs
  have hg := allocatedFixedPathLiftDensity_zero_off_ball B short R σ
    (fun j => (hR j).ne') hB lower width hwidth hamin hδ
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample) hr y.2 hy
  change _ * allocatedFixedPathLiftDensity B short R σ hB lower width (noise sample) y.2 = 0
  rw [hg, mul_zero]

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_zero_of_norm_gt_two
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (hz : ∀ a, |z a| ≤ 1) (y : Domain) (hy : 2 < ‖y‖) : density sample y = 0 := by
  rcases (lt_max_iff.mp hy) with hsp | hactive
  · have hf := fixedSpatialEmptyDensity_zero_outside
      (fixedSpatialKernelDensity e W L z h0 h1)
      (fixedSpatialKernelDensity_zero_of_norm_gt_two e W L z h0 h1 hW hL hsize hz)
      y.1 hsp
    change fixedSpatialEmptyDensity (fixedSpatialKernelDensity e W L z h0 h1) y.1 * _ = 0
    rw [hf, zero_mul]
  · exact fixedSpatialKernelOriginalForecastDensity_zero_of_active_norm_gt_two B U basis hR hσ S
      e W L z h0 h1 hB lower width hδ hw hl sample hs hwidth y hactive

include hR hσ hδ hw hl hs in
theorem fixedSpatialKernelOriginalForecastDensity_compact
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (hz : ∀ a, |z a| ≤ 1) : HasCompactSupport (density sample) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Domain) 2)
  intro y hy
  apply fixedSpatialKernelOriginalForecastDensity_zero_of_norm_gt_two B U basis hR hσ S
    e W L z h0 h1 hB lower width hδ hw hl sample hs hwidth hW hL hsize hz y
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (lowerG widthG : G → ℝ)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
variable (hwG : ∀ g, widthG g ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "frame" => fixedSpatialKernelSliceFrame W L z lowerG widthG
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG false h0 hwG
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG true h1 hwG
local notation "A₀" => fixedSpatialKernelBlockEquiv e W L frame false h0slice
local notation "A₁" => fixedSpatialKernelBlockEquiv e W L frame true h1slice

noncomputable def fixedSpatialKernelSliceOriginalForecastDensity (sample : Sample) : Domain → ℝ :=
  fixedSpatialKernelOriginalForecastDensity B U basis S e W L frame h0slice h1slice
    hB lowerP widthP sample

local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z
  lowerG widthG h0 h1 hwG hB lowerP widthP

variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_image_law :
    ((unitBoxMeasure G).prod (unitBoxMeasure Input)).map
      (fun p => (fixedSpatialKernelMap W L z (fun g => lowerG g + widthG g * p.1 g),
        allocatedOriginalSampleLiftMap B U basis S lowerP widthP sample p.2)) =
      realDensityMeasure volume (density sample) := by
  simpa only [fixedSpatialKernelOriginalForecastSource, fixedSpatialKernelMap_slice,
    fixedSpatialKernelSliceOriginalForecastDensity] using
    (fixedSpatialKernelOriginalForecastSource_density B U basis hR hσ S
      e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs)

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_probability_data :
    (∀ y, 0 ≤ density sample y) ∧ Integrable (density sample) ∧
      (∫ y, density sample y) = 1 :=
  fixedSpatialKernelOriginalForecastDensity_probability_data B U basis hR hσ S
    e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_bounds :
    (∀ y, density sample y ∈ Set.Icc (0 : ℝ) (fixedSpatialOriginalForecastCap B A₁ hδP)) ∧
      LipschitzWith (fixedSpatialOriginalForecastLip B A₀ A₁ hδP) (density sample) :=
  fixedSpatialKernelOriginalForecastDensity_bounds B U basis hR hσ S
    e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) :
    (∫ y, φ y ∂realDensityMeasure volume (density sample)) =
      ∫ p, φ (fixedSpatialKernelMap W L z (fun g => lowerG g + widthG g * p.1 g),
        allocatedOriginalSampleLiftMap B U basis S lowerP widthP sample p.2)
        ∂(unitBoxMeasure G).prod (unitBoxMeasure Input) := by
  simpa only [fixedSpatialKernelMap_slice, fixedSpatialKernelSliceOriginalForecastDensity] using
    (fixedSpatialKernelOriginalForecastDensity_test_integral B U basis hR hσ S
      e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs φ hφ)

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_zero_of_active_norm_gt_two
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    (y : Domain) (hy : 2 < ‖y.2‖) : density sample y = 0 :=
  fixedSpatialKernelOriginalForecastDensity_zero_of_active_norm_gt_two B U basis hR hσ S
    e W L frame h0slice h1slice hB lowerP widthP hδP hwP hlP sample hs hwidthP y hy

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (hz : ∀ a, |z a| ≤ 1) (hlG : ∀ g, 0 ≤ lowerG g) (hwG0 : ∀ g, 0 ≤ widthG g)
    (hcontained : ∀ g, lowerG g + widthG g ≤ 1)
    (y : Domain) (hy : 2 < ‖y‖) : density sample y = 0 := by
  rcases lt_max_iff.mp hy with hsp | hactive
  · have hf := fixedSpatialEmptyDensity_zero_outside
      (fixedSpatialKernelSliceDensity e W L z lowerG widthG h0 h1 hwG)
      (fixedSpatialKernelSliceDensity_zero_of_norm_gt_two e W L z lowerG widthG h0 h1 hwG
        hW hL hsize hz hlG hwG0 hcontained) y.1 hsp
    change fixedSpatialEmptyDensity
      (fixedSpatialKernelSliceDensity e W L z lowerG widthG h0 h1 hwG) y.1 * _ = 0
    rw [hf, zero_mul]
  · exact fixedSpatialKernelSliceOriginalForecastDensity_zero_of_active_norm_gt_two
      B U basis hR hσ S e W L z lowerG widthG h0 h1 hwG hB lowerP widthP
      hδP hwP hlP sample hs hwidthP y hactive

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelSliceOriginalForecastDensity_compact
    (hwidthP : ∀ a p, |lowerP a p| + |widthP a p| ≤ 1)
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (hz : ∀ a, |z a| ≤ 1) (hlG : ∀ g, 0 ≤ lowerG g) (hwG0 : ∀ g, 0 ≤ widthG g)
    (hcontained : ∀ g, lowerG g + widthG g ≤ 1) : HasCompactSupport (density sample) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Domain) 2)
  intro y hy
  apply fixedSpatialKernelSliceOriginalForecastDensity_zero_of_norm_gt_two
    B U basis hR hσ S e W L z lowerG widthG h0 h1 hwG hB lowerP widthP
    hδP hwP hlP sample hs hwidthP hW hL hsize hz hlG hwG0 hcontained y
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem fixedSpatialKernelProgression_width_pos {S H : ℕ} {step : ℤ}
    (hS : 0 < S) (hstep : 0 < step) (hH : 2 ≤ H) :
    (0 : ℝ) < (step : ℝ) * ((H - 1 : ℕ) : ℝ) / S := by
  apply div_pos
  · apply mul_pos
    · exact_mod_cast hstep
    · exact_mod_cast (show 0 < H - 1 by omega)
  · exact_mod_cast hS

end Erdos3

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

variable (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ) (z : Option G × X → ℝ)
variable (start : G → ℤ) (step : ℤ) (H : G → ℕ)
variable (hstep : 0 < step) (hH : ∀ g, 2 ≤ H g)
local notation "lowerG" => (fun g => (start g : ℝ) / S.value)
local notation "widthG" => (fun g => (step : ℝ) * ((H g - 1 : ℕ) : ℝ) / S.value)
variable (h0 : (fixedSpatialKernelBlock e W L z false).det ≠ 0)
  (h1 : (fixedSpatialKernelBlock e W L z true).det ≠ 0)
local notation "hwG" => (fun g => ne_of_gt (fixedSpatialKernelProgression_width_pos S.positive hstep (hH g)))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lowerP widthP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

local notation "frame" => fixedSpatialKernelSliceFrame W L z lowerG widthG
local notation "h0slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG false h0 hwG
local notation "h1slice" => fixedSpatialKernelBlock_slice_det_ne_zero e W L z lowerG widthG true h1 hwG
local notation "A₀" => fixedSpatialKernelBlockEquiv e W L frame false h0slice
local notation "A₁" => fixedSpatialKernelBlockEquiv e W L frame true h1slice

local notation "density" => fixedSpatialKernelSliceOriginalForecastDensity B U basis S e W L z
  lowerG widthG h0 h1 hwG hB lowerP widthP

variable {δP : ℝ} (hδP : 0 < δP)
  (hwP : ∀ a p, δP ≤ widthP a p) (hlP : ∀ a p, 0 ≤ lowerP a p)
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
  (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j)
    (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelProgressionForecastDensity_iterated_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    (∫ y, φ y ∂realDensityMeasure volume (density sample)) =
      ∫ k, ∫ v, φ (fixedSpatialKernelMap W L z
        (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value),
        allocatedOriginalSampleLiftMap B U basis S lowerP widthP sample v)
        ∂unitBoxMeasure Input ∂unitBoxMeasure G := by
  rw [fixedSpatialKernelSliceOriginalForecastDensity_test_integral B U basis hR hσ S
    e W L z lowerG widthG h0 h1 hwG hB lowerP widthP hδP hwP hlP sample hs φ hφ]
  have hparam (k : G → ℝ) :
      (fun g => lowerG g + widthG g * k g) =
      (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value) := by
    funext g
    dsimp only
    ring
  simp_rw [hparam]
  apply integral_prod
  refine ⟨?_, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun p => hbound _))⟩
  apply Measurable.aestronglyMeasurable
  apply hφ.comp
  apply Measurable.prodMk
  · unfold fixedSpatialKernelMap
    fun_prop
  · exact (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lowerP widthP sample).comp
      measurable_snd

include hR hσ hδP hwP hlP hs in
theorem fixedSpatialKernelProgressionForecastDensity_scalarCube_iterated_test_integral
    (φ : Domain → ℂ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    (∫ y, φ y ∂realDensityMeasure volume (density sample)) =
      ∫ k, ∫ v, φ (fixedSpatialKernelMap W L z
        (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g none) / S.value),
        allocatedOriginalSampleLiftMap B U basis S lowerP widthP sample v)
        ∂unitBoxMeasure Input ∂scalarCubeProductMeasure G Empty := by
  rw [fixedSpatialKernelProgressionForecastDensity_iterated_test_integral
    B U basis hR hσ S e W L z start step H hstep hH h0 h1 hB lowerP widthP
    hδP hwP hlP sample hs φ hφ hbound]
  let F := fun (k : G → ℝ) (v : Input → ℝ) => φ (fixedSpatialKernelMap W L z
    (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value),
    allocatedOriginalSampleLiftMap B U basis S lowerP widthP sample v)
  have hF : Measurable (Function.uncurry F) := by
    apply hφ.comp
    apply Measurable.prodMk
    · unfold fixedSpatialKernelMap
      fun_prop
    · exact (allocatedOriginalSampleLiftMap_fixed_measurable B U basis S lowerP widthP sample).comp
        measurable_snd
  have hm : Measurable (fun k : G → Option Empty → ℝ => fun g => k g none) := by fun_prop
  change (∫ k, ∫ v, F k v ∂unitBoxMeasure Input ∂unitBoxMeasure G) = _
  rw [← scalarCubeProductMeasure_empty_map G]
  exact integral_map hm.aemeasurable hF.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable

end Erdos3.VectorPolynomial

end

end OAI
