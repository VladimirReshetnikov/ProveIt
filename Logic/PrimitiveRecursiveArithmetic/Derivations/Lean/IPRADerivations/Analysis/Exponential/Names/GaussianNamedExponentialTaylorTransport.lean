import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialShiftDerivative
import IPRADerivations.Analysis.Trigonometry.Cyclic.GaussianCyclicExponentialSamples
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTAConstants
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateComposition

/-!
# Exponential increments with an independently certified linear term

A small exponent increment and a quadratic estimate for its linear
approximation give a first-order estimate on original exponential
names, with independently chosen admitted endpoint radii.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianNamedExponentialTaylorTransport

open_ipra
open GaussianCyclicExponentialSamples (sampleBound exponential_bound)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialRadiusIndependence (independent_radii_proper input_widen same_input_cross)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedDifferenceRate (rate_parameters_congr self_rate)
open GaussianNamedInverseRate (independentRate)
open GaussianRadiusExponentialName (nameF data input name_regular)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "Shift" => GaussianNamedExponentialShiftDerivative.incrementF
local notation "sd" => GaussianNamedExponentialShiftDerivative.incrementData
local notation "Weighted" => GaussianNamedExponentialShiftDerivative.weightedF
local notation "wd" => GaussianNamedExponentialShiftDerivative.weightedData

def gain (R : PTm n) : PTm n := two*sampleBound R+two
def numerator (R A C : PTm n) : PTm n := gain R*(A*A)+sampleBound R*C

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (gain R) = gain (Syn.subst σ R) := by simp [gain,two]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (R A C : PTm n) :
    Syn.subst σ (numerator R A C) = numerator (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ C) :=
  by simp [numerator]

theorem exponential_samples (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound (nameF f) (data R x) (sampleBound R) := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have h' : Γ.map Fm.shift ⊢[PRAAx] input f (sh R) (sh x) := by simpa [sh,Fm.shift,Syn.shift] using hf.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,sh,GaussianRadiusExponentialName.subst_data,
    GaussianCyclicExponentialSamples.subst_sampleBound] using exponential_bound f (sh R) (sh x) (var 0) h'

theorem radius_from_sample (f : PR 2) (x S : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (ap2 f zero x) S one) :
    Γ ⊢[PRAAx] le (U f x) (two*S+two) := by
  let q := ap2 f zero x
  let C := GaussianRationalL1.qL1 q
  let d := RationalSupMetric.denominatorOf C
  let a := RationalIntegerNormalization.positivePart (RationalSupMetric.numeratorOf C)
  let M := two*S
  have hd := RationalArgmin.denominator_positive (Γ := Γ) C
  have order := GaussianRationalL1Algebra.qL1_of_bounded q S one (le_refl one) hf
  have clear := GaussianRationalMetric.comparison_to_cleared C (GaussianEuclideanDistanceName.fraction M one) a M d one
    (GaussianGeneralFTAConstants.l1_natural_representation q)
    (GaussianEuclideanDistanceName.fraction_represents M one (le_refl _)) order
  have numle : Γ ⊢[PRAAx] le a (d*M) := le_congr (one_mul _) (mul_comm _ _) clear
  exact add_le_add_right two (GaussianDescentClockArithmetic.ceiling_least a d M hd numle)

theorem rate (f g ℓ : PR 2) (R R₀ R₁ x v y w A B C : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hf : Γ ⊢[PRAAx] input f R x)
    (hx : Γ ⊢[PRAAx] input f R₀ x) (hv : Γ ⊢[PRAAx] input f R₁ v)
    (hs : Γ ⊢[PRAAx] GaussianNamedExponentialLinearRate.source g y A B)
    (hw : Γ ⊢[PRAAx] pointCN ℓ w)
    (he : Γ ⊢[PRAAx] crossEquivalent (addF f g) f (addData x y) v)
    (hr : Γ ⊢[PRAAx] independentRate g ℓ y w C (B*B)) :
    Γ ⊢[PRAAx] independentRate (Diff (nameF f) (nameF f)) (multiplyF (nameF f) ℓ)
      (dd (data R₁ v) (data R₀ x)) (multiplyData (nameF f) ℓ (data R₀ x) w) (numerator R A C) (B*B) := by
  let E := nameF f
  let D := B*B
  let a := data R x
  let b := data R₀ x
  let c := data R₁ v
  let s := GaussianExponentialAddition.sumData R x y
  let S := GaussianExponentialAddition.sumF f g
  let t := wd f g R x y
  let P := multiplyF E ℓ
  let u := multiplyData E ℓ a w
  let u₀ := multiplyData E ℓ b w
  let F := Shift f g
  let V := Diff E E
  have hD := positive_product _ _ hs.andE₁ hs.andE₁
  have hg := hs.andE₂.andE₂.andE₁
  have ha := name_regular f R x hf
  have hb := name_regular f R₀ x hx
  have hc := name_regular f R₁ v hv
  have gy := GaussianNamedExponentialLinearRate.unit_input g y A B hs
  have hh := GaussianExponentialReference.add_input f g R x y hf (input_widen g one R y gy hR)
  have hS : Γ ⊢[PRAAx] pointCN S s := name_regular (addF f g) (R+R) (addData x y) hh
  have base := same_input_cross f R₀ R x hx hf
  have changed := independent_radii_proper (addF f g) f (R+R) R₁ (addData x y) v hh hv he
  have inc := difference_proper E S E E c s b a hc hS hb ha (cross_symm _ _ _ _ changed) base
  have lin := GaussianGammaAdjacentCutoff.multiply_cross E E ℓ ℓ b a w w hb ha hw hw base (cross_refl _ _ hw)
  have raw := GaussianNamedExponentialShiftDerivative.independent_rate f g R x y A B hR hf hs
  have cmp : Γ ⊢[PRAAx] le (GaussianNamedExponentialShiftDerivative.coefficient f R x A*D) (gain R*(A*A)*D) :=
    le_mul_mono (le_mul_mono (radius_from_sample E a (sampleBound R) (exponential_bound f R x zero hf)) (le_refl _)) (le_refl _)
  have first := GaussianNamedRateRadius.weaken F (Weighted f g) (sd R x y) t _ D _ D hD hD cmp raw
  have mul := GaussianNamedMultiplyRate.independent_rate E g E ℓ a y a w zero one C D (U g y) (sampleBound R)
    (le_refl one) hD ha hg ha hw (GaussianNameBounds.all_samples_bounded g y hg) (exponential_samples f R x hf)
    (self_rate E a ha) hr
  have second : Γ ⊢[PRAAx] independentRate (Weighted f g) P t u (sampleBound R*C) D :=
    rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) mul
  have joined := GaussianNamedRateComposition.same_denominator F (Weighted f g) P (sd R x y) t u _ D _ hD first second
  exact GaussianNamedRateTransport.transport F P V P (sd R x y) u (dd c b) u₀ (numerator R A C) D hD joined inc lin

end LeanProofs.IPRA.Analysis.GaussianNamedExponentialTaylorTransport
