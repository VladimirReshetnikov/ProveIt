import IPRADerivations.Analysis.GaussianEulerPositivePowerChartMeshJacobian
import IPRADerivations.Analysis.GaussianEulerCompactModulus
import IPRADerivations.Analysis.RationalGaussianNameEmbedding

/-!
# Literal positive rational corrected chart images

The actual raw decoder is retained before adding the exact scalar tilt.
Its new numerator is A*U+2*i*B and its denominator is B*U. A common
query paying 2*N<=U keeps every corrected image in [1/G,H+1]. The
original compact Euler rate compares corrected and raw decoded rows at
independent requested queries, with leading error L*2*N/U.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartCorrectedImage

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChartMesh (source timeNumerator timeDenominator node correctedNode node_source)
open GaussianEulerPositivePowerChartMeshJacobian (correctedPoint)
open GaussianEulerPositivePowerChartImage (query reciprocalMargin)
open GaussianEulerPositivePowerChart (majorant)
open GaussianUnitIntervalInputDecoding (numerator denominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd positive_product canonical_unique ofGaussian_represents ofGaussian_canonical)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def input (k e f d h Q S E T a C N : PTm n) : Fm PTm n :=
  source e f d h Q S E T a C N ⋏ le (two*N) (unit (query k h Q E T))
def imageNumerator (k i e f d h Q S E T a C N : PTm n) : PTm n :=
  numerator (node k i e f d h Q S E T a C N)*unit (query k h Q E T)+two*i*denominator (node k i e f d h Q S E T a C N)
def imageDenominator (k i e f d h Q S E T a C N : PTm n) : PTm n :=
  denominator (node k i e f d h Q S E T a C N)*unit (query k h Q E T)
def imageFraction (k i e f d h Q S E T a C N : PTm n) : PTm n :=
  fraction (imageNumerator k i e f d h Q S E T a C N) (imageDenominator k i e f d h Q S E T a C N)
def imageData (k i e f d h Q S E T a C N : PTm n) : PTm n :=
  pairT (imageNumerator k i e f d h Q S E T a C N) (imageDenominator k i e f d h Q S E T a C N)

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (k e f d h Q S E T a C N : PTm n) :
    (input k e f d h Q S E T a C N).subst σ = input (Syn.subst σ k) (Syn.subst σ e) (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h)
      (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [input]
@[simp] theorem subst_imageNumerator {m : ℕ} (σ : Fin n → PTm m) (k i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (imageNumerator k i e f d h Q S E T a C N) = imageNumerator (Syn.subst σ k) (Syn.subst σ i) (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [imageNumerator]
@[simp] theorem subst_imageDenominator {m : ℕ} (σ : Fin n → PTm m) (k i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (imageDenominator k i e f d h Q S E T a C N) = imageDenominator (Syn.subst σ k) (Syn.subst σ i) (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [imageDenominator]
@[simp] theorem subst_imageFraction {m : ℕ} (σ : Fin n → PTm m) (k i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (imageFraction k i e f d h Q S E T a C N) = imageFraction (Syn.subst σ k) (Syn.subst σ i) (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [imageFraction]
@[simp] theorem subst_imageData {m : ℕ} (σ : Fin n → PTm m) (k i e f d h Q S E T a C N : PTm n) :
    Syn.subst σ (imageData k i e f d h Q S E T a C N) = imageData (Syn.subst σ k) (Syn.subst σ i) (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ N) := by simp [imageData]

theorem fraction_sum (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    qadd (fraction A B) (fraction C D) ≐ fraction (A*D+C*B) (B*D) := by
  have first := GaussianRationalHorner.represents_rescale _ _ _ D (ofGaussian_represents (ComplexLogarithmRemainder.scale A ComplexLogarithmRemainder.oneCode) B hB)
  have second := GaussianRationalHorner.represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm D B)
    (GaussianRationalHorner.represents_rescale _ _ _ B (ofGaussian_represents (ComplexLogarithmRemainder.scale C ComplexLogarithmRemainder.oneCode) D hD))
  have both := GaussianRationalHorner.qadd_represents _ _ _ _ (B*D) (positive_product _ _ hB hD) first second
  apply canonical_unique _ _ (ComplexLogarithmRemainder.scale (A*D+C*B) ComplexLogarithmRemainder.oneCode) (B*D)
    (GaussianRationalHorner.qadd_canonical _ _) (ofGaussian_canonical _ _ (positive_product _ _ hB hD)) (positive_product _ _ hB hD)
    (hrv := ofGaussian_represents _ _ (positive_product _ _ hB hD))
  apply GaussianRationalHorner.represents_congr (.eqRefl _) ?_ (.eqRefl _) both
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring

/-- Exact literal rational decoding, retaining the original raw decoder. -/
theorem fraction_exact (k i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    imageFraction k i e f d h Q S E T a C N ≐ correctedPoint k i e f d h Q S E T a C N := by
  have raw := GaussianEulerPositivePowerChartImage.fraction_exact k e f d h Q S E T _ _ (node_source i e f d h Q S E T a C N hs hi)
  exact ((fraction_sum _ _ (two*i) _ (GaussianUnitIntervalInputDecoding.denominator_positive _) (unit_positive _)).eqSymm.eqTrans
    (GaussianRationalSyntheticDivision.qadd_congr raw (.eqRefl _))).eqTrans
      (GaussianEulerPositivePowerChartMeshJacobian.corrected_point_at k i e f d h Q S E T a C N hs).eqSymm

theorem corrected_domain (k i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain (imageNumerator k i e f d h Q S E T a C N) (imageDenominator k i e f d h Q S E T a C N)
      (reciprocalMargin h Q E T) (majorant Q S E T+one) := by
  have raw := GaussianEulerPositivePowerChartMesh.actual_image_domain k i e f d h Q S E T a C N hs.andE₁ hi
  have numerator_positive := positive_product _ _ raw.andE₁.andE₁ (unit_positive (query k h Q E T))
  refine .andI (.andI (le_trans numerator_positive (le_add_right _ _)) (positive_product _ _ raw.andE₁.andE₂ (unit_positive _))) (.andI ?_ ?_)
  · unfold imageNumerator imageDenominator
    ipra_le 𝔞(unit (query k h Q E T))*sl raw.andE₂.andE₁+
      𝔞(reciprocalMargin h Q E T*two*i*denominator (node k i e f d h Q S E T a C N))
  · unfold imageNumerator imageDenominator
    ipra_le 𝔞(unit (query k h Q E T))*sl raw.andE₂.andE₂+
      𝔞(denominator (node k i e f d h Q S E T a C N))*sl hs.andE₂+
      𝔞(two*denominator (node k i e f d h Q S E T a C N))*sl hi

theorem raw_common_domain (k i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain (numerator (node k i e f d h Q S E T a C N)) (denominator (node k i e f d h Q S E T a C N))
      (reciprocalMargin h Q E T) (majorant Q S E T+one) := by
  have raw := GaussianEulerPositivePowerChartMesh.actual_image_domain k i e f d h Q S E T a C N hs hi
  exact .andI raw.andE₁ (.andI raw.andE₂.andE₁ (le_trans raw.andE₂.andE₂
    (le_of_eq_add (d := denominator (node k i e f d h Q S E T a C N)) (by ipra_ring))))

theorem original_displacement (k i e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    distanceBounded (imageFraction k i e f d h Q S E T a C N)
      (fraction (numerator (node k i e f d h Q S E T a C N)) (denominator (node k i e f d h Q S E T a C N)))
      (two*N) (unit (query k h Q E T)) := by
  have real := GaussianEulerPositivePowerChartLower.original_sample_real (query k h Q E T) e f d h S
    (timeNumerator i N a C) (timeDenominator N E) hs.andE₁.andE₁.andE₂ hs.andE₁.andE₂.andE₁.andE₂
  have raw := GaussianEulerPositivePowerChartImage.fraction_exact k e f d h Q S E T _ _ (node_source i e f d h Q S E T a C N hs hi)
  have moved := RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (unit_positive (query k h Q E T))
    (GaussianEulerPositivePowerChartMesh.corrected_displacement k i e f d h Q S E T a C N hi)
  exact GaussianRationalDistanceOrder.distance_congr (fraction_exact k i e f d h Q S E T a C N hs hi).eqSymm
    ((RationalGaussianEmbedding.canonical_axis_roundtrip _ real.andE₁ real.andE₂).eqTrans raw.eqSymm) (.eqRefl _) (.eqRefl _) moved

/-- The original Euler names and both requested clocks remain unchanged. -/
theorem original_Euler_rate (k i z R B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N)
    (hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B (reciprocalMargin h Q E T)) : Γ ⊢[PRAAx]
    independentRate GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF
      (GaussianEulerIntegrandName.data z B (imageNumerator k i e f d h Q S E T a C N) (imageDenominator k i e f d h Q S E T a C N))
      (GaussianEulerIntegrandName.data z B (numerator (node k i e f d h Q S E T a C N)) (denominator (node k i e f d h Q S E T a C N)))
      (GaussianEulerCompactModulus.lipschitz R (reciprocalMargin h Q E T) (majorant Q S E T+one)*(two*N)) (unit (query k h Q E T)) :=
  GaussianEulerCompactModulus.original_rate _ _ _ _ _ _ _ _ _ _ _
    (.andI hz (.andI (corrected_domain k i e f d h Q S E T a C N hs hi)
      (.andI (raw_common_domain k i e f d h Q S E T a C N hs.andE₁ hi)
        (.andI (unit_positive _) (original_displacement k i e f d h Q S E T a C N hs.andE₁ hi)))))

theorem original_Euler_observations (p q k i z R B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] input k e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N)
    (hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B (reciprocalMargin h Q E T)) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 GaussianEulerIntegrandName.nameF p (GaussianEulerIntegrandName.data z B (imageNumerator k i e f d h Q S E T a C N) (imageDenominator k i e f d h Q S E T a C N)))
      (ap2 GaussianEulerIntegrandName.nameF q (GaussianEulerIntegrandName.data z B (numerator (node k i e f d h Q S E T a C N)) (denominator (node k i e f d h Q S E T a C N))))
      (GaussianNamedInverseRate.rateNumerator (GaussianEulerCompactModulus.lipschitz R (reciprocalMargin h Q E T) (majorant Q S E T+one)*(two*N)) (unit (query k h Q E T)) p q)
      (GaussianNamedInverseRate.rateDenominator (unit (query k h Q E T)) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_Euler_rate k i z R B e f d h Q S E T a C N hs hi hz)

theorem actual_corrected_power_chart_literal_positive_image_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    ((input (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⋏ le (var 1) (var 12)) ⟶
      (GaussianCompactLogarithmBounds.domain
        (imageNumerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (imageDenominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (reciprocalMargin (var 5) (var 6) (var 8) (var 9)) (majorant (var 6) (var 7) (var 8) (var 9)+one) ⋏
      imageFraction (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ≐
        correctedPoint (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))) :=
  closeUniv 13 (.impI (.andI (corrected_domain _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (fraction_exact _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₂)))

theorem actual_corrected_power_chart_original_Euler_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
    ((input (var 0) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15) ⋏
      (le (var 1) (var 15) ⋏ GaussianEulerExponentCompactBounds.source (var 2) (var 3) (var 4) (reciprocalMargin (var 8) (var 9) (var 11) (var 12)))) ⟶
    independentRate GaussianEulerIntegrandName.nameF GaussianEulerIntegrandName.nameF
      (GaussianEulerIntegrandName.data (var 2) (var 4)
        (imageNumerator (var 0) (var 1) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15))
        (imageDenominator (var 0) (var 1) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15)))
      (GaussianEulerIntegrandName.data (var 2) (var 4)
        (numerator (node (var 0) (var 1) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15)))
        (denominator (node (var 0) (var 1) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15))))
      (GaussianEulerCompactModulus.lipschitz (var 3) (reciprocalMargin (var 8) (var 9) (var 11) (var 12)) (majorant (var 9) (var 10) (var 11) (var 12)+one)*(two*var 15))
      (unit (query (var 0) (var 8) (var 9) (var 11) (var 12)))) :=
  closeUniv 16 (.impI (original_Euler_rate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartCorrectedImage
