/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

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
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree short
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty) short sides
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedOriginalSampleFullSliceMap (sample : Sample) (y : Input → ℝ) (o : Output) : ℝ :=
  MvPolynomial.eval (fun k => MvPolynomial.eval y
      (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k))
    (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) /
      R o.1.val.1

theorem allocatedOriginalSampleFullSliceMap_eq_eval (sample : Sample) (y : Input → ℝ) (o : Output) :
    allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y o =
      MvPolynomial.eval (allocatedOriginalSampleSliceInput B U basis S x u lower width y)
        (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) /
          R o.1.val.1 := by
  simp only [allocatedOriginalSampleFullSliceMap, allocatedOriginalSampleSliceSubstitution_eval]

noncomputable def allocatedOriginalSampleTailNoise (t : ℝ) (sample : Sample) : Coeff → ℝ :=
  activeTailRescale degree short (fun a => σ a.1 / t) (noise sample)

include hR hσ in
theorem allocatedOriginalSampleFullSliceMap_eq_profile (sample : Sample) {t : ℝ} (ht : t ≠ 0) :
    allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample =
      jointSlicedProfileValue degree Subtype.val (fun _ => 1 / 4)
        (unitProfilePrincipalSize (B := B)) (unitProfileTailSize (G := G) (B := B) degree)
        (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩)
        (fun _ => allocatedOriginalSampleSliceSubstitution B U basis S x u lower width) t := by
  let r := noise sample
  let coeff := fun (a : Active) e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩
  let ξ := fun _ : Active => allocatedOriginalSampleSliceSubstitution B U basis S x u lower width
  have htail (j : Fin m) (N : ℕ) : tailProfileSize (R j) (σ j) N =
      σ j * tailProfileSize (R j) 1 N := by unfold tailProfileSize; ring
  have hpoly (a : Active) :
      monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B degree a.val =>
        coefficientProfileCenter (principalCoefficientSlots degree a.val)
            (principalProfileSize (R a.val.1) (Fintype.card (B a.val))) e +
          coefficientProfileWidth (principalCoefficientSlots degree a.val) (constantCoefficientSlot _ _)
            (R a.val.1 / 4) (principalProfileSize (R a.val.1) (Fintype.card (B a.val)))
            (t * tailProfileSize (R a.val.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a.val))) e *
              coeff a e) =
        monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample a.val) := by
    rw [← allocatedSampleProfileNoise_polynomial B U basis hR hσ S sample a.val,
      allocatedAxisProfilePolynomial_eq]
    apply congrArg (monomialArrayPolynomial Subtype.val)
    funext e
    rw [htail]
    unfold coeff allocatedOriginalSampleTailNoise activeTailRescale
    congr 1
    exact boundedProfileWidth_noise_rescale degree a.val (R a.val.1 / 4)
      (principalProfileSize (R a.val.1) (Fintype.card (B a.val)))
      (tailProfileSize (R a.val.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a.val)))
      (σ a.val.1) t (allocatedSampleProfileNoise B U basis S sample a.val e) ht e
  funext y o
  change MvPolynomial.eval (fun k => MvPolynomial.eval y (ξ o.1 k)) _ / R o.1.val.1 = _
  rw [← hpoly o.1]
  change jointSlicedProfileValue degree Subtype.val (fun a => R a.1 / 4)
      (fun a => principalProfileSize (R a.1) (Fintype.card (B a)))
      (fun a => tailProfileSize (R a.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a)))
      coeff ξ t y o / R o.1.val.1 = _
  rw [jointSlicedProfileValue_unit_scale degree Subtype.val (fun a => R a.1) coeff ξ t y]
  exact mul_div_cancel_left₀ _ (hR o.1.val.1).ne'

include hR hσ in
theorem allocatedOriginalSampleLiftMap_eq_tail_ideal (sample : Sample) (t : ℝ) :
    allocatedOriginalSampleLiftMap B U basis S lower width sample =
      fun y => jointSlicedProfileShift degree Subtype.val (fun _ => 1 / 4)
          (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩) +
        jointSlicedPrincipal
          (jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
            (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩)) lower width y := by
  rw [allocatedOriginalSampleLiftMap_eq_fixedPath B U basis S lower width hR hσ sample]
  unfold allocatedFixedPathLiftMap
  rw [allocatedFixedPathPrincipal_eq B short R σ (fun j => (hR j).ne'),
    allocatedFixedPathShift_eq B short R σ (fun j => (hR j).ne')]
  have hc : jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
      (fun a e => noise sample ⟨a, e⟩) =
      jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
        (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩) := by
    funext a b
    simp only [jointSlicedProfilePrincipal, allocatedOriginalSampleTailNoise, activeTailRescale_principal]
  have hs : (fun o : Output => (1 / 4 : ℝ) * noise sample ⟨o.1, constantCoefficientSlot _ _⟩) =
      jointSlicedProfileShift degree Subtype.val (fun _ => 1 / 4)
        (fun a e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩) := by
    funext o
    simp only [jointSlicedProfileShift, allocatedOriginalSampleTailNoise, activeTailRescale_constant]
  rw [hc, hs]

theorem allocatedOriginalSampleFullSliceMap_measurable (sample : Sample) :
    Measurable (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample) := by
  apply Measurable.of_eval
  intro o
  have hi : Continuous (fun y : Input → ℝ => fun k => MvPolynomial.eval y
      (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k)) :=
    continuous_pi (fun k => MvPolynomial.continuous_eval _)
  exact (((MvPolynomial.continuous_eval
    (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val))).comp hi).div_const
      (R o.1.val.1)).measurable

include hR hσ in
theorem allocatedOriginalSample_slice_real_perturbation
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (b : ∀ a : Active, B a.val)
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hw : ∀ a i, δ ≤ width a (b a, i))
    (hlower : ∀ a i, 0 ≤ lower a (b a, i))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (hsmall : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) δ A η)
    (φ : (Output → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ z, ‖φ z‖ ≤ 1) :
    |(∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y) ∂unitBoxMeasure Input) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input| ≤ η := by
  let coeff := fun (a : Active) e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩
  have hcoeff (a : Active) (e : SamplerCoefficientSlot G B degree a.val) : |coeff a e| ≤ 1 :=
    activeTailRescale_abs_le degree short (fun a => σ a.1 / t)
      (allocatedTailRatio_abs_le ht hσbound) (noise sample)
      (allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs) ⟨a, e⟩
  have he := jointSlicedProfileValue_unit_comparison degree (Subtype.val : Active → LayerSamplerAxis I n)
    (m := m) (fun a => Nat.zero_lt_succ _) (fun a => Nat.succ_le_of_lt a.val.1.isLt)
    (fun _ => 1 / 4) coeff hcoeff
    (fun _ => allocatedOriginalSampleSliceSubstitution B U basis S x u lower width)
    (fun _ k => allocatedOriginalSampleSliceSubstitution_degree B U basis S x u lower width k)
    (fun _ k => allocatedOriginalSampleSliceSubstitution_mass B U basis S x u lower width hwidth k)
    lower width
    (fun a b i => allocatedOriginalSampleSliceSubstitution_principal B U basis S x u lower width a b i)
    hwidth b (fun _ => ⟨0, Nat.zero_lt_succ _⟩)
    (unitProfilePrincipalLowerBound_pos B) hδ hδone hη
    (fun a => unitProfilePrincipalLowerBound_le B a.val) hw (fun a i _ => hlower a i)
    A hA t hsmall φ hφ hbound
  rw [allocatedOriginalSampleLiftMap_eq_tail_ideal B U basis hR hσ S lower width sample t,
    allocatedOriginalSampleFullSliceMap_eq_profile B U basis hR hσ S x u lower width sample ht.ne']
  exact he

include hR hσ in
theorem allocatedOriginalSample_slice_complex_perturbation
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (b : ∀ a : Active, B a.val)
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hw : ∀ a i, δ ≤ width a (b a, i))
    (hlower : ∀ a i, 0 ≤ lower a (b a, i))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (hsmall : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) δ A η)
    (φ : (Output → ℝ) → ℂ) (hφ : Measurable φ) (hbound : ∀ z, ‖φ z‖ ≤ 1) :
    ‖(∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y) ∂unitBoxMeasure Input) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input‖ ≤ 2 * η := by
  let f := fun y => φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
  let g := fun y => φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
  have hif : Integrable f (unitBoxMeasure Input) :=
    ⟨(hφ.comp ((allocatedOriginalSampleLiftMap_measurable B U basis S lower width).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hbound _))⟩
  have hig : Integrable g (unitBoxMeasure Input) :=
    ⟨(hφ.comp (allocatedOriginalSampleFullSliceMap_measurable B U basis S x u lower width sample)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hbound _))⟩
  have hre := allocatedOriginalSample_slice_real_perturbation B U basis hR hσ S x u lower width
    sample hs hwidth b hδ hδone hη hw hlower A hA ht hσbound hsmall
    (fun y => (φ y).re) (Complex.measurable_re.comp hφ)
    (fun y => (Complex.abs_re_le_norm _).trans (hbound y))
  have him := allocatedOriginalSample_slice_real_perturbation B U basis hR hσ S x u lower width
    sample hs hwidth b hδ hδone hη hw hlower A hA ht hσbound hsmall
    (fun y => (φ y).im) (Complex.measurable_im.comp hφ)
    (fun y => (Complex.abs_im_le_norm _).trans (hbound y))
  have hfre : (∫ y, f y ∂unitBoxMeasure Input).re = ∫ y, (f y).re ∂unitBoxMeasure Input := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hif).symm
  have hgre : (∫ y, g y ∂unitBoxMeasure Input).re = ∫ y, (g y).re ∂unitBoxMeasure Input := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hig).symm
  have hfim : (∫ y, f y ∂unitBoxMeasure Input).im = ∫ y, (f y).im ∂unitBoxMeasure Input := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hif).symm
  have hgim : (∫ y, g y ∂unitBoxMeasure Input).im = ∫ y, (g y).im ∂unitBoxMeasure Input := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hig).symm
  change ‖(∫ y, f y ∂unitBoxMeasure Input) - ∫ y, g y ∂unitBoxMeasure Input‖ ≤ _
  calc
    _ ≤ |((∫ y, f y ∂unitBoxMeasure Input) - ∫ y, g y ∂unitBoxMeasure Input).re| +
        |((∫ y, f y ∂unitBoxMeasure Input) - ∫ y, g y ∂unitBoxMeasure Input).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ η + η := by
      apply add_le_add
      · rw [Complex.sub_re, hfre, hgre]
        exact hre
      · rw [Complex.sub_im, hfim, hgim]
        exact him
    _ = _ := by ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

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
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

noncomputable def allocatedOriginalSampleFullSliceLip (t : ℝ) : ℝ≥0 :=
  (1 + Real.toNNReal |t|) * allocatedOriginalSampleLiftLip B U basis S

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

theorem allocatedOriginalSampleFullSliceMap_affine (sample : Sample)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ) (y : Input → ℝ) :
    allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample
        (fun j => lower j.1 j.2 + width j.1 j.2 * y j) =
      allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y := by
  have hi : allocatedOriginalSampleSliceInput B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
      (fun j => lower j.1 j.2 + width j.1 j.2 * y j) =
      allocatedOriginalSampleSliceInput B U basis S x u lower width y := by
    funext k
    rcases k with g | ⟨a, b, i⟩
    · rfl
    · by_cases ha : short a <;> simp [allocatedOriginalSampleSliceInput, ha]
  funext o
  simp only [allocatedOriginalSampleFullSliceMap_eq_eval, hi]

theorem allocatedOriginalSampleFullSliceMap_supported_lipschitzOn
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t) :
    LipschitzOnWith (allocatedOriginalSampleFullSliceLip B U basis S t)
      (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample)
      (Metric.closedBall 0 1) := by
  let coeff := fun (a : Active) e => allocatedOriginalSampleTailNoise B U basis S t sample ⟨a, e⟩
  let ξ := fun _ : Active => allocatedOriginalSampleSliceSubstitution B U basis S x u lower width
  let tail : Output → MvPolynomial Input ℝ :=
    jointSlicedProfileTail degree Subtype.val (unitProfileTailSize (G := G) (B := B) degree) coeff ξ
  have hcoeff (a : Active) (e : SamplerCoefficientSlot G B degree a.val) : |coeff a e| ≤ 1 :=
    activeTailRescale_abs_le degree short (fun a => σ a.1 / t)
      (allocatedTailRatio_abs_le ht hσbound) (noise sample)
      (allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs) ⟨a, e⟩
  have hmass (o : Output) : realPolynomialMass (tail o) ≤ 1 :=
    slicedProfileTailPolynomial_unit_mass degree o.1.val (coeff o.1) (hcoeff o.1) (ξ o.1)
      (allocatedOriginalSampleSliceSubstitution_mass B U basis S x u lower width hwidth)
  have hdegree (o : Output) : (tail o).totalDegree ≤ m :=
    (slicedProfileTailPolynomial_degree degree o.1.val _ (coeff o.1) (ξ o.1)
      (allocatedOriginalSampleSliceSubstitution_degree B U basis S x u lower width)).trans
        (Nat.succ_le_of_lt o.1.val.1.isLt)
  have htail : LipschitzOnWith (allocatedOriginalSampleLiftLip B U basis S)
      (polynomialVectorMap tail) (Metric.closedBall 0 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y _ => (polynomialVectorMap_contDiff tail).differentiable (by norm_num) y)
      _ (convex_closedBall 0 1)
    intro y hy
    have hy' : ∀ i, |y i| ≤ 1 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hy
      intro i
      exact (norm_le_pi_norm y i).trans hy
    have he := (polynomialVectorMap_mass_c2_bounds tail
      (fun o i => (MvPolynomial.degreeOf_le_totalDegree _ _).trans (hdegree o))
      zero_le_one hmass y hy').2.1
    change ‖fderiv ℝ (polynomialVectorMap tail) y‖ ≤
      (allocatedOriginalSampleLiftLip B U basis S : ℝ)
    simpa only [allocatedOriginalSampleLiftLip, NNReal.coe_mul, NNReal.coe_natCast, mul_one] using he
  have hideal := allocatedOriginalSampleLiftMap_supported_lipschitzOn
    B U basis hR hσ S sample hs lower width hwidth
  have hsplit : allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample =
      fun y => allocatedOriginalSampleLiftMap B U basis S lower width sample y +
        t • polynomialVectorMap tail y := by
    rw [allocatedOriginalSampleFullSliceMap_eq_profile B U basis hR hσ S x u lower width sample ht.ne',
      allocatedOriginalSampleLiftMap_eq_tail_ideal B U basis hR hσ S lower width sample t]
    exact jointSlicedProfileValue_split degree Subtype.val (fun _ => Nat.zero_lt_succ _)
      (fun _ => 1 / 4) (unitProfilePrincipalSize (B := B))
      (unitProfileTailSize (G := G) (B := B) degree) coeff ξ lower width
      (allocatedOriginalSampleSliceSubstitution_principal B U basis S x u lower width) t
  rw [hsplit]
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  calc
    _ ≤ dist (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
          (allocatedOriginalSampleLiftMap B U basis S lower width sample z) +
        dist (t • polynomialVectorMap tail y) (t • polynomialVectorMap tail z) :=
      dist_add_add_le _ _ _ _
    _ ≤ (allocatedOriginalSampleLiftLip B U basis S : ℝ) * dist y z +
        |t| * ((allocatedOriginalSampleLiftLip B U basis S : ℝ) * dist y z) := by
      apply add_le_add (hideal.dist_le_mul y hy z hz)
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using htail.dist_le_mul y hy z hz) (abs_nonneg t)
    _ = _ := by
      simp only [allocatedOriginalSampleFullSliceLip, NNReal.coe_mul, NNReal.coe_add,
        NNReal.coe_one, Real.coe_toNNReal _ (abs_nonneg t)]
      ring

end Erdos3.VectorPolynomial

end

end OAI
