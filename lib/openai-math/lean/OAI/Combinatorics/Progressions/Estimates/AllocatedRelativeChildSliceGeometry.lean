/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.RelativeChildSliceGeometry
import OAI.Combinatorics.Progressions.Geometry.AllocatedEnormousProfileSupport
import OAI.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

noncomputable def allocatedSampleNormalizedCoefficients (sample : Sample) :
    (a : LayerSamplerAxis I n) → SamplerCoefficientSlot G B degree a → ℝ
  | ⟨j, .inl i⟩, e => (sample j).1 i e / allocatedContinuousProfileScales B U basis S j e
  | ⟨j, .inr i⟩, e => ((sample j).2 i e : ℝ) / allocatedIntegerProfileScales B U basis S j i e

noncomputable def allocatedSampleProfileNoise (sample : Sample) :
    (a : LayerSamplerAxis I n) → SamplerCoefficientSlot G B degree a → ℝ
  | ⟨j, .inl i⟩, e =>
    (allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inl i⟩ e -
      allocatedContinuousProfileCenters B R j i e) / allocatedContinuousProfileWidths B R σ j i e
  | ⟨j, .inr i⟩, e =>
    (allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e -
      allocatedIntegerProfileCenters B R j i e) / allocatedIntegerProfileWidths B R σ j i e

include hR hσ in
theorem allocatedSampleProfileNoise_polynomial (sample : Sample) (a : LayerSamplerAxis I n) :
    allocatedAxisProfilePolynomial B R σ a (allocatedSampleProfileNoise B U basis S sample a) =
      monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample a) := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i =>
    unfold allocatedAxisProfilePolynomial
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    dsimp only [allocatedSampleProfileNoise]
    field_simp [(allocatedContinuousProfileWidths_pos B hR hσ j i e).ne']
    ring
  | inr i =>
    unfold allocatedAxisProfilePolynomial
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    dsimp only [allocatedSampleProfileNoise]
    field_simp [(allocatedIntegerProfileWidths_pos B hR hσ j i e).ne']
    ring

noncomputable def allocatedSampleActiveProfileNoise (sample : Sample) :
    ActiveProfileCoefficientIndex G B degree grid → ℝ :=
  fun e => allocatedSampleProfileNoise B U basis S sample e.1.val e.2

theorem allocatedSampleActiveProfileNoise_measurable :
    Measurable (allocatedSampleActiveProfileNoise B U basis S) := by
  apply Measurable.of_eval
  rintro ⟨⟨⟨j, i⟩, ha⟩, e⟩
  cases i with
  | inl i =>
    simp only [allocatedSampleActiveProfileNoise, allocatedSampleProfileNoise,
      allocatedSampleNormalizedCoefficients]
    fun_prop
  | inr i =>
    simp only [allocatedSampleActiveProfileNoise, allocatedSampleProfileNoise,
      allocatedSampleNormalizedCoefficients]
    fun_prop

include hR hσ in
theorem allocatedFixedPathPrincipal_of_sample (sample : Sample)
    (a : {a // ¬grid a}) (b : B a.val) :
    allocatedFixedPathPrincipal B grid R σ (allocatedSampleActiveProfileNoise B U basis S sample) a b =
      allocatedSampleNormalizedCoefficients B U basis S sample a.val
        (principalCoefficientSlot degree a.val b) / R a.val.1 := by
  unfold allocatedFixedPathPrincipal
  change (allocatedAxisProfilePolynomial B R σ a.val
    (allocatedSampleProfileNoise B U basis S sample a.val)).coeff _ / _ = _
  rw [allocatedSampleProfileNoise_polynomial B U basis hR hσ S]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (principalCoefficientSlot degree a.val b).val / _ = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]

include hR hσ in
theorem allocatedFixedPathShift_of_sample (sample : Sample) (a : {a // ¬grid a}) :
    allocatedFixedPathShift B grid R σ (allocatedSampleActiveProfileNoise B U basis S sample) a =
      allocatedSampleNormalizedCoefficients B U basis S sample a.val
        (constantCoefficientSlot vars (degree a.val)) / R a.val.1 := by
  unfold allocatedFixedPathShift
  change (allocatedAxisProfilePolynomial B R σ a.val
    (allocatedSampleProfileNoise B U basis S sample a.val)).coeff _ / _ = _
  rw [allocatedSampleProfileNoise_polynomial B U basis hR hσ S]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (constantCoefficientSlot vars (degree a.val)).val / _ = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]

private theorem normalized_profile_noise_abs_le {c w x : ℝ} (hw : 0 < w)
    (hx : affineProbabilityProfile c w x ≠ 0) : |(x - c) / w| ≤ 1 := by
  rw [abs_div, abs_of_pos hw]
  apply (div_le_one hw).mpr
  have hs := affineProbabilityProfile_support c hw hx
  linarith

include hR hσ in
theorem allocatedSampleProfileNoise_continuous_bound (sample : Sample) (j : Fin m) (i : I j)
    (hs : affineProductProfile (allocatedLayerCenters B U basis S j i)
      (allocatedLayerWidths B U basis S j i) ((sample j).1 i) ≠ 0)
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inl i⟩ e| ≤ 1 := by
  have he := (Finset.prod_ne_zero_iff.mp hs) e (Finset.mem_univ e)
  rw [allocatedLayerCenters_scale, allocatedLayerWidths_scale] at he
  have hscale := allocatedContinuousProfileScales_pos B U basis S j e
  have hwidth := allocatedContinuousProfileWidths_pos B hR hσ j i e
  have hb := affineProbabilityProfile_support _ (mul_pos hscale hwidth) he
  have hn : |(sample j).1 i e / allocatedContinuousProfileScales B U basis S j e -
      allocatedContinuousProfileCenters B R j i e| ≤
      allocatedContinuousProfileWidths B R σ j i e := by
    have heq : (sample j).1 i e / allocatedContinuousProfileScales B U basis S j e -
        allocatedContinuousProfileCenters B R j i e =
        ((sample j).1 i e - allocatedContinuousProfileScales B U basis S j e *
          allocatedContinuousProfileCenters B R j i e) / allocatedContinuousProfileScales B U basis S j e := by
      field_simp
    rw [heq, abs_div, abs_of_pos hscale]
    apply (div_le_iff₀ hscale).mpr
    nlinarith
  dsimp only [allocatedSampleProfileNoise, allocatedSampleNormalizedCoefficients]
  rw [abs_div, abs_of_pos hwidth]
  exact (div_le_one hwidth).mpr hn

include hR hσ in
theorem allocatedSampleProfileNoise_integer_bound (sample : Sample) (j : Fin m) (i : Fin (n j))
    (hσ1 : σ j ≤ 1) (henormous : S.value ^ (layerTailDegree m + 1) < basisAxisScale (basis j) i)
    (hs : ∀ e, (sample j).2 i e ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i e).support)
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inr i⟩ e| ≤ 1 := by
  have hp := allocatedEnormousProfile_support_of_coordinate_support
    B U basis hR hσ S j i hσ1 henormous ((sample j).2 i) hs
  exact normalized_profile_noise_abs_le (allocatedIntegerProfileWidths_pos B hR hσ j i e)
    ((Finset.prod_ne_zero_iff.mp hp) e (Finset.mem_univ e))

include hR hσ in
theorem allocatedSampleActiveProfileNoise_abs_le (hσ1 : ∀ j, σ j ≤ 1) (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (e : ActiveProfileCoefficientIndex G B degree grid) :
    |allocatedSampleActiveProfileNoise B U basis S sample e| ≤ 1 := by
  rcases e with ⟨⟨⟨j, i⟩, ha⟩, e⟩
  have hrows := (mixedArraySupported_iff_rows _ _ _ (sample j)).mp (hs j)
  cases i with
  | inl i =>
    exact allocatedSampleProfileNoise_continuous_bound B U basis hR hσ S sample j i (hrows.1 i) e
  | inr i =>
    exact allocatedSampleProfileNoise_integer_bound B U basis hR hσ S sample j i
      (hσ1 j) (Nat.lt_of_not_ge ha) (hrows.2 i) e

include hR hσ in
theorem allocatedSampleActiveProfileNoise_ae_abs_le (hσ1 : ∀ j, σ j ≤ 1) :
    ∀ᵐ sample ∂allocatedCoefficientSource B U basis hR hσ S,
      ∀ e, |allocatedSampleActiveProfileNoise B U basis S sample e| ≤ 1 := by
  let μ := fun j => mixedScalarArrayLaw (allocatedLayerCenters B U basis S j)
    (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j)
  let : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    mixedScalarArrayLaw_probability _ _ (allocatedLayerWidths_pos B U basis hR hσ S j) _
  have hs : ∀ᵐ sample ∂Measure.pi μ, ∀ j,
      mixedArraySupported (allocatedLayerCenters B U basis S j)
        (allocatedLayerWidths B U basis S j)
        (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j) :=
    ae_all_iff.mpr (fun j => (Measure.quasiMeasurePreserving_eval μ j).ae
      (mixedScalarArrayLaw_support _ _ (allocatedLayerWidths_pos B U basis hR hσ S j) _))
  exact hs.mono (fun sample hs =>
    allocatedSampleActiveProfileNoise_abs_le B U basis hR hσ S hσ1 sample hs)

theorem allocatedSampleNormalizedCoefficients_continuous (sample : Sample) (j : Fin m) (i : I j)
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inl i⟩ e =
      (sample j).1 i e * monomialScale (layerSamplerBox B U basis S) e.val := by
  simp [allocatedSampleNormalizedCoefficients, allocatedContinuousProfileScales]

theorem allocatedSampleNormalizedCoefficients_integer (sample : Sample) (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e =
      ((sample j).2 i e : ℝ) * monomialScale (layerSamplerBox B U basis S) e.val /
        (basisAxisScale (basis j) i : ℝ) := by
  simp only [allocatedSampleNormalizedCoefficients, allocatedIntegerProfileScales, div_div_eq_mul_div]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

include hR hσ in
theorem allocatedSampleProfileNoise_active_integer_coordinate_bound
    (sample : Sample) (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (e : BoundedCoefficientExponent vars (j.val + 1))
    (he : (sample j).2 i e ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i e).support) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inr i⟩ e| ≤ 1 := by
  have hb := integerPolynomialCoordinatePMF_active_profile_bound
    (P := layerIntegerPrincipalSlots B j i) (j₀ := constantCoefficientSlot _ _)
    (h := j.val + 1) (K := basisAxisScale (basis j) i) (L := S.value) (s := layerTailDegree m)
    (hh := Nat.zero_lt_succ _) (hK := basisAxisScale_pos (basis j) i) (hL := S.positive)
    (T := layerSamplerBox B U basis S)
    (hT := fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (hTL := layerSamplerBox_le B U basis S) (e := Subtype.val)
    (he := fun d => d.property.trans (layerDegree_le_tailDegree j))
    (ρ := R j / 4)
    (γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)
    (ε := tailProfileSize (R j) (σ j)
      (Fintype.card (BoundedCoefficientExponent vars (j.val + 1))))
    (hρ := div_pos (hR j) (by norm_num)) (hγ := principalProfileSize_pos (hR j) _)
    (hε := tailProfileSize_pos (hR j) (hσ j) _)
    (hgap := S.gap j i) (hεL := S.width j)
    (hj₀ := layerIntegerPrincipalSlots_not_constant B j i) (he₀ := rfl)
    (hprincipal := layerSamplerSides_integer_principal B U basis R S.value j i)
    hactive e he
  have hb' : |allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e -
      allocatedIntegerProfileCenters B R j i e| ≤ allocatedIntegerProfileWidths B R σ j i e := by
    simpa only [allocatedSampleNormalizedCoefficients, allocatedIntegerProfileScales,
      allocatedIntegerProfileCenters, allocatedIntegerProfileWidths,
      div_div_eq_mul_div, div_mul_eq_mul_div] using hb
  have hw := allocatedIntegerProfileWidths_pos B hR hσ j i e
  change |(allocatedSampleNormalizedCoefficients B U basis S sample ⟨j, .inr i⟩ e -
    allocatedIntegerProfileCenters B R j i e) / allocatedIntegerProfileWidths B R σ j i e| ≤ 1
  rw [abs_div, abs_of_pos hw]
  exact (div_le_one hw).mpr hb'

include hR hσ in
theorem allocatedSampleProfileNoise_active_integer_bound
    (sample : Sample) (j : Fin m) (i : Fin (n j))
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (hs : ∀ e, (sample j).2 i e ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i e).support)
    (e : BoundedCoefficientExponent vars (j.val + 1)) :
    |allocatedSampleProfileNoise B U basis S sample ⟨j, .inr i⟩ e| ≤ 1 :=
  allocatedSampleProfileNoise_active_integer_coordinate_bound B U basis hR hσ S sample j i hactive e (hs e)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

def allocatedShortAxis (L : ℕ) : LayerSamplerAxis I n → Prop
  | ⟨_, .inl _⟩ => False
  | ⟨j, .inr i⟩ => basisAxisScale (basis j) i ≤ L ^ (j.val + 1)

noncomputable instance allocatedShortAxisDecidable (L : ℕ) :
    DecidablePred (allocatedShortAxis (I := I) U basis L) := Classical.decPred _

theorem allocatedPrincipalSides_long_of_not_short (a : LayerSamplerAxis I n)
    (ha : ¬allocatedShortAxis (I := I) U basis S.value a) (b : B a) (v : Fin (degree a)) :
    allocatedPrincipalSides B U basis S ⟨a, b, v⟩ = S.value := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i => rfl
  | inr i =>
    have hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i := Nat.lt_of_not_ge ha
    simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
      layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
      integerAxisSideLength, hactive, ↓reduceIte]

variable (P : LayerSamplerAxis I n → Prop)

noncomputable def allocatedSampleRestrictedProfileNoise (sample : Sample) :
    ActiveProfileCoefficientIndex G B degree P → ℝ :=
  fun e => allocatedSampleProfileNoise B U basis S sample e.1.val e.2

theorem allocatedSampleRestrictedProfileNoise_measurable :
    Measurable (allocatedSampleRestrictedProfileNoise B U basis S P) := by
  apply Measurable.of_eval
  rintro ⟨⟨⟨j, i⟩, ha⟩, e⟩
  cases i with
  | inl i =>
    simp only [allocatedSampleRestrictedProfileNoise, allocatedSampleProfileNoise,
      allocatedSampleNormalizedCoefficients]
    fun_prop
  | inr i =>
    simp only [allocatedSampleRestrictedProfileNoise, allocatedSampleProfileNoise,
      allocatedSampleNormalizedCoefficients]
    fun_prop

include hR hσ in
theorem allocatedFixedPathPrincipal_of_restricted_sample (sample : Sample)
    (a : {a // ¬P a}) (b : B a.val) :
    allocatedFixedPathPrincipal B P R σ (allocatedSampleRestrictedProfileNoise B U basis S P sample) a b =
      allocatedSampleNormalizedCoefficients B U basis S sample a.val
        (principalCoefficientSlot degree a.val b) / R a.val.1 := by
  unfold allocatedFixedPathPrincipal
  change (allocatedAxisProfilePolynomial B R σ a.val
    (allocatedSampleProfileNoise B U basis S sample a.val)).coeff _ / _ = _
  rw [allocatedSampleProfileNoise_polynomial B U basis hR hσ S]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (principalCoefficientSlot degree a.val b).val / _ = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]

include hR hσ in
theorem allocatedFixedPathShift_of_restricted_sample (sample : Sample) (a : {a // ¬P a}) :
    allocatedFixedPathShift B P R σ (allocatedSampleRestrictedProfileNoise B U basis S P sample) a =
      allocatedSampleNormalizedCoefficients B U basis S sample a.val
        (constantCoefficientSlot vars (degree a.val)) / R a.val.1 := by
  unfold allocatedFixedPathShift
  change (allocatedAxisProfilePolynomial B R σ a.val
    (allocatedSampleProfileNoise B U basis S sample a.val)).coeff _ / _ = _
  rw [allocatedSampleProfileNoise_polynomial B U basis hR hσ S]
  change (monomialArrayPolynomial Subtype.val _).coeff
    (constantCoefficientSlot vars (degree a.val)).val / _ = _
  rw [monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

noncomputable def allocatedOriginalSamplePrincipal (sample : Sample) (a : Active) (b : B a.val) : ℝ :=
  allocatedSampleNormalizedCoefficients B U basis S sample a.val
    (principalCoefficientSlot degree a.val b) / R a.val.1

noncomputable def allocatedOriginalSampleShift (sample : Sample) (a : Active) : ℝ :=
  allocatedSampleNormalizedCoefficients B U basis S sample a.val
    (constantCoefficientSlot vars (degree a.val)) / R a.val.1

variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedOriginalSampleLiftMap (sample : Sample) (x : Input → ℝ) : Output → ℝ :=
  (fun o => allocatedOriginalSampleShift B U basis S sample o.1) +
    jointSlicedPrincipal (allocatedOriginalSamplePrincipal B U basis S sample) lower width x

theorem allocatedOriginalSampleLiftMap_apply (sample : Sample) (x : Input → ℝ) (o : Output) :
    allocatedOriginalSampleLiftMap B U basis S lower width sample x o =
      allocatedSampleNormalizedCoefficients B U basis S sample o.1.val
        (constantCoefficientSlot vars (degree o.1.val)) / R o.1.val.1 +
      ∑ b, (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val
        (principalCoefficientSlot degree o.1.val b) / R o.1.val.1) *
        ∏ v, (lower o.1 (b, v) + width o.1 (b, v) * x ⟨o.1, b, v⟩) := rfl

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

include hR hσ in
theorem allocatedOriginalSamplePrincipal_eq_fixedPath (sample : Sample) :
    allocatedOriginalSamplePrincipal B U basis S sample =
      allocatedFixedPathPrincipal B short R σ
        (allocatedSampleRestrictedProfileNoise B U basis S short sample) := by
  funext a b
  exact (allocatedFixedPathPrincipal_of_restricted_sample B U basis hR hσ S short sample a b).symm

include hR hσ in
theorem allocatedOriginalSampleShift_eq_fixedPath (sample : Sample) :
    allocatedOriginalSampleShift B U basis S sample =
      allocatedFixedPathShift B short R σ
        (allocatedSampleRestrictedProfileNoise B U basis S short sample) := by
  funext a
  exact (allocatedFixedPathShift_of_restricted_sample B U basis hR hσ S short sample a).symm

include hR hσ in
theorem allocatedOriginalSampleLiftMap_eq_fixedPath (sample : Sample) :
    allocatedOriginalSampleLiftMap B U basis S lower width sample =
      allocatedFixedPathLiftMap B short R σ lower width
        (allocatedSampleRestrictedProfileNoise B U basis S short sample) := by
  funext x
  unfold allocatedOriginalSampleLiftMap allocatedFixedPathLiftMap
  rw [allocatedOriginalSamplePrincipal_eq_fixedPath B U basis S hR hσ sample,
    allocatedOriginalSampleShift_eq_fixedPath B U basis S hR hσ sample]

theorem allocatedOriginalSampleLiftMap_measurable :
    Measurable (fun p : Sample × (Input → ℝ) =>
      allocatedOriginalSampleLiftMap B U basis S lower width p.1 p.2) := by
  apply Measurable.of_eval
  rintro ⟨⟨⟨j, i⟩, ha⟩, u⟩
  cases i with
  | inl i =>
    simp only [allocatedOriginalSampleLiftMap_apply, allocatedSampleNormalizedCoefficients]
    fun_prop
  | inr i =>
    simp only [allocatedOriginalSampleLiftMap_apply, allocatedSampleNormalizedCoefficients]
    fun_prop

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedOriginalSampleSliceSubstitution : vars → MvPolynomial Input ℝ
  | .inl g => MvPolynomial.C ((x g none : ℝ) / S.value)
  | .inr ⟨a, b, i⟩ =>
      if ha : short a then
        MvPolynomial.C ((u ⟨⟨a, ha⟩, b, i⟩ none : ℝ) / sides ⟨a, b, i⟩)
      else MvPolynomial.C (lower ⟨a, ha⟩ (b, i)) +
        MvPolynomial.C (width ⟨a, ha⟩ (b, i)) * MvPolynomial.X ⟨⟨a, ha⟩, b, i⟩

theorem allocatedOriginalSampleSliceSubstitution_principal
    (a : Active) (b : B a.val) (i : Fin (degree a.val)) :
    allocatedOriginalSampleSliceSubstitution B U basis S x u lower width (.inr ⟨a.val, b, i⟩) =
      MvPolynomial.C (lower a (b, i)) +
        MvPolynomial.C (width a (b, i)) * MvPolynomial.X ⟨a, b, i⟩ := by
  simp only [allocatedOriginalSampleSliceSubstitution, a.property, ↓reduceDIte]

theorem allocatedOriginalSampleSliceSubstitution_degree (k : vars) :
    (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k).totalDegree ≤ 1 := by
  rcases k with g | ⟨a, b, i⟩
  · simp [allocatedOriginalSampleSliceSubstitution]
  · by_cases ha : short a
    · simp [allocatedOriginalSampleSliceSubstitution, ha]
    · simp only [allocatedOriginalSampleSliceSubstitution, ha, ↓reduceDIte]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (by simp)
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem allocatedOriginalSampleSliceSubstitution_mass
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1) (k : vars) :
    realPolynomialMass (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k) ≤ 1 := by
  rcases k with g | ⟨a, b, i⟩
  · have hb := (norm_le_pi_norm (fun t => (x g t : ℝ) / (S.value : ℝ)) none).trans
      (integerScalarCubeBox_normalized_norm_le S.positive (x g))
    simpa only [allocatedOriginalSampleSliceSubstitution, realPolynomialMass_C, Real.norm_eq_abs] using hb
  · by_cases ha : short a
    · have hb := (norm_le_pi_norm
        (fun t => (u ⟨⟨a, ha⟩, b, i⟩ t : ℝ) / (sides ⟨a, b, i⟩ : ℝ)) none).trans
        (integerScalarCubeBox_normalized_norm_le (allocatedPrincipalSides_pos B U basis S ⟨a, b, i⟩)
          (u ⟨⟨a, ha⟩, b, i⟩))
      simpa only [allocatedOriginalSampleSliceSubstitution, ha, ↓reduceDIte,
        realPolynomialMass_C, Real.norm_eq_abs] using hb
    · simp only [allocatedOriginalSampleSliceSubstitution, ha, ↓reduceDIte]
      apply (realPolynomialMass_add_le _ _).trans
      apply le_trans _ (hwidth ⟨a, ha⟩ (b, i))
      rw [realPolynomialMass_C]
      apply add_le_add le_rfl
      simpa only [realPolynomialMass_X, mul_one] using
        realPolynomialMass_C_mul_le (width ⟨a, ha⟩ (b, i))
          (MvPolynomial.X (⟨⟨a, ha⟩, b, i⟩ : Input))

noncomputable def allocatedOriginalSampleSliceInput (y : Input → ℝ) : vars → ℝ
  | .inl g => (x g none : ℝ) / S.value
  | .inr ⟨a, b, i⟩ =>
      if ha : short a then (u ⟨⟨a, ha⟩, b, i⟩ none : ℝ) / sides ⟨a, b, i⟩
      else lower ⟨a, ha⟩ (b, i) + width ⟨a, ha⟩ (b, i) * y ⟨⟨a, ha⟩, b, i⟩

theorem allocatedOriginalSampleSliceSubstitution_eval (y : Input → ℝ) (k : vars) :
    MvPolynomial.eval y (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k) =
      allocatedOriginalSampleSliceInput B U basis S x u lower width y k := by
  rcases k with g | ⟨a, b, i⟩
  · simp only [allocatedOriginalSampleSliceSubstitution, allocatedOriginalSampleSliceInput,
      MvPolynomial.eval_C]
  · by_cases ha : short a <;>
      simp [allocatedOriginalSampleSliceSubstitution, allocatedOriginalSampleSliceInput, ha]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical
open Module

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (scale : LayerSamplerScale (G := G) B U basis R σ)

local notation "Vars" => LayerSamplerVariables G I n B
local notation "sides" => Sum.elim (fun _ : G => scale.value) (allocatedPrincipalSides B U basis scale)

def allocatedChildKernelCoordinate {H : ℕ} (hH : H ≤ scale.value) (g : G) :
    {k : Vars // H ≤ sides k} := ⟨Sum.inl g, hH⟩

def allocatedChildActiveCoordinate {H : ℕ} (hH : H ≤ scale.value)
    (j : Fin m) (i : Fin (n j))
    (hactive : scale.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
    {k : Vars // H ≤ sides k} :=
  ⟨Sum.inr ⟨⟨j, Sum.inr i⟩, a, v⟩, by
    change H ≤ allocatedPrincipalSides B U basis scale _
    rw [allocatedPrincipalSides_active B U basis scale j i hactive a v]
    exact hH⟩

theorem allocatedChildActiveCoordinate_side {H : ℕ} (hH : H ≤ scale.value)
    (j : Fin m) (i : Fin (n j))
    (hactive : scale.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
    sides (allocatedChildActiveCoordinate B U basis scale hH j i hactive a v).val =
      scale.value :=
  allocatedPrincipalSides_active B U basis scale j i hactive a v

theorem allocatedChildSlice_long_coordinate_geometry
    {H q : ℕ} (slice : ResidueBoxSlice (fun k : {k : Vars // H ≤ sides k} => sides k) q)
    (hq : 0 < q) {cost : ℝ}
    (hlarge : 2 * Real.exp cost ≤ (scale.value : ℝ))
    (hfraction : ∀ k, Real.exp (-cost) * (sides k.val : ℝ) ≤ slice.length k)
    (k : {k : Vars // H ≤ sides k}) (hk : sides k.val = scale.value) :
    2 ≤ slice.length k ∧
      0 ≤ (slice.start k : ℝ) / scale.value ∧
      Real.exp (-cost) / 2 ≤ (q : ℝ) * ((slice.length k : ℝ) - 1) / scale.value ∧
      |(slice.start k : ℝ) / scale.value| +
        |(q : ℝ) * ((slice.length k : ℝ) - 1) / scale.value| ≤ 1 := by
  have hg := slice.normalized_endpoint_geometry k hq (by simpa only [hk] using hlarge)
    (hfraction k)
  simpa only [hk] using hg

theorem allocatedChildSlice_kernel_geometry
    {H q : ℕ} (hH : H ≤ scale.value)
    (slice : ResidueBoxSlice (fun k : {k : Vars // H ≤ sides k} => sides k) q)
    (hq : 0 < q) {cost : ℝ}
    (hlarge : 2 * Real.exp cost ≤ (scale.value : ℝ))
    (hfraction : ∀ k, Real.exp (-cost) * (sides k.val : ℝ) ≤ slice.length k)
    (g : G) :
    let k := allocatedChildKernelCoordinate B U basis scale hH g
    2 ≤ slice.length k ∧
      0 ≤ (slice.start k : ℝ) / scale.value ∧
      Real.exp (-cost) / 2 ≤ (q : ℝ) * ((slice.length k : ℝ) - 1) / scale.value ∧
      |(slice.start k : ℝ) / scale.value| +
        |(q : ℝ) * ((slice.length k : ℝ) - 1) / scale.value| ≤ 1 :=
  allocatedChildSlice_long_coordinate_geometry B U basis scale slice hq hlarge hfraction _ rfl

theorem allocatedChildSlice_active_geometry
    {H q : ℕ} (hH : H ≤ scale.value)
    (slice : ResidueBoxSlice (fun k : {k : Vars // H ≤ sides k} => sides k) q)
    (hq : 0 < q) {cost : ℝ}
    (hlarge : 2 * Real.exp cost ≤ (scale.value : ℝ))
    (hfraction : ∀ k, Real.exp (-cost) * (sides k.val : ℝ) ≤ slice.length k)
    (j : Fin m) (i : Fin (n j))
    (hactive : scale.value ^ (j.val + 1) < basisAxisScale (basis j) i)
    (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)) :
    let k := allocatedChildActiveCoordinate B U basis scale hH j i hactive a v
    2 ≤ slice.length k ∧
      0 ≤ (slice.start k : ℝ) / scale.value ∧
      Real.exp (-cost) / 2 ≤ (q : ℝ) * ((slice.length k : ℝ) - 1) / scale.value ∧
      |(slice.start k : ℝ) / scale.value| +
        |(q : ℝ) * ((slice.length k : ℝ) - 1) / scale.value| ≤ 1 :=
  allocatedChildSlice_long_coordinate_geometry B U basis scale slice hq hlarge hfraction _
    (allocatedChildActiveCoordinate_side B U basis scale hH j i hactive a v)

theorem allocatedChildSlice_stride_le [Nonempty G]
    {H q : ℕ} (hH : H ≤ scale.value)
    (slice : ResidueBoxSlice (fun k : {k : Vars // H ≤ sides k} => sides k) q)
    (hq : 0 < q) {cost : ℝ}
    (hlarge : 2 * Real.exp cost ≤ (scale.value : ℝ))
    (hfraction : ∀ k, Real.exp (-cost) * (sides k.val : ℝ) ≤ slice.length k) :
    (q : ℝ) ≤ 2 * Real.exp cost := by
  let k := allocatedChildKernelCoordinate B U basis scale hH (Classical.choice inferInstance)
  exact (slice.stride_le_exp_cost (i := k) hq hlarge (hfraction k)).2

def allocatedChildNonshortCoordinate {H : ℕ} (hH : H ≤ scale.value)
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis scale.value a})
    (b : B a.val) (v : Fin (layerSamplerDegree I n a.val)) :
    {k : Vars // H ≤ sides k} :=
  ⟨Sum.inr ⟨a.val, b, v⟩, by
    change H ≤ allocatedPrincipalSides B U basis scale _
    rw [allocatedPrincipalSides_long_of_not_short B U basis scale a.val a.property b v]
    exact hH⟩

theorem allocatedChildNonshortCoordinate_side {H : ℕ} (hH : H ≤ scale.value)
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis scale.value a})
    (b : B a.val) (v : Fin (layerSamplerDegree I n a.val)) :
    sides (allocatedChildNonshortCoordinate B U basis scale hH a b v).val = scale.value :=
  allocatedPrincipalSides_long_of_not_short B U basis scale a.val a.property b v

theorem allocatedChildSlice_nonshort_geometry
    {H q : ℕ} (hH : H ≤ scale.value)
    (slice : ResidueBoxSlice (fun k : {k : Vars // H ≤ sides k} => sides k) q)
    (hq : 0 < q) {cost : ℝ}
    (hlarge : 2 * Real.exp cost ≤ (scale.value : ℝ))
    (hfraction : ∀ k, Real.exp (-cost) * (sides k.val : ℝ) ≤ slice.length k)
    (a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis scale.value a})
    (b : B a.val) (v : Fin (layerSamplerDegree I n a.val)) :
    let k := allocatedChildNonshortCoordinate B U basis scale hH a b v
    2 ≤ slice.length k ∧
      0 ≤ (slice.start k : ℝ) / scale.value ∧
      Real.exp (-cost) / 2 ≤ (q : ℝ) * ((slice.length k : ℝ) - 1) / scale.value ∧
      |(slice.start k : ℝ) / scale.value| +
        |(q : ℝ) * ((slice.length k : ℝ) - 1) / scale.value| ≤ 1 :=
  allocatedChildSlice_long_coordinate_geometry B U basis scale slice hq hlarge hfraction _
    (allocatedChildNonshortCoordinate_side B U basis scale hH a b v)

end Erdos3.VectorPolynomial

end

end OAI
