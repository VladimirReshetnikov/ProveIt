import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentNamed
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentTwoSidedMargin
import IPRADerivations.Analysis.Gamma.Names.Derivatives.GaussianNamedGammaIncrementInput

/-!
# Actual named moment shifts and their common rational chart

Both signed translates use the original normalized constant-addition
program. Their observations at the same clock are translates of one
actual base observation. Projecting the two translated observations
to their real parts preserves those exact translated fractions.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamedShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceMomentBackwardWindow (lowerNumerator lowerData)
open GaussianBinetLaplaceMomentForwardMargin (upperRadius upper_source)
open GaussianBinetLaplaceMomentImproper (data nameF)
open GaussianBinetLaplaceMomentRescale (rational_proper)
open GaussianBinetLaplaceMomentSignedVariation (pointData projected_source)
open GaussianBinetLaplaceMomentTwoSidedMargin (lower_source window_geometry)
open GaussianDominantPairAlgebra (radiusNumerator radius_numerator_norm scalar_representation_cross)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (radius)
open GaussianNamedGammaIncrementInput (incrementF incrementData sample_at)
open GaussianNamedRightHalfPlane (threshold)
open GaussianNamedRightHalfPlaneSigned (certificate realNumerator denominator native_value)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (ofGaussian ofGaussian_represents scalar_congr positive_product)
open GaussianRationalL1 (rawGaussian raw_represents)
open GaussianRationalMetric (bounded bounded_of_cleared)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "baseSource" => GaussianNamedRightHalfPlane.source
local notation "shiftSource" => GaussianNamedGammaIncrementInput.source
local notation "shiftClock" => GaussianNamedGammaIncrementInput.clock
local notation "rationalSource" => GaussianBinetLaplaceMomentTwoSidedMargin.source
local notation "real" => ComplexLogarithmRemainder.re

def negativeStep (H : PTm n) : PTm n := ComplexLogarithmRemainder.neg (radiusNumerator H)

def source (f : PR 2) (x M H Q : PTm n) : Fm PTm n :=
  baseSource f x M ⋏ (le one H ⋏ (le one Q ⋏ le ((num 4*M)*H) Q))

@[simp] theorem subst_negativeStep {m : ℕ} (σ : Fin n → PTm m) (H : PTm n) :
    Syn.subst σ (negativeStep H) = negativeStep (Syn.subst σ H) := by
  simp [negativeStep]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x M H Q : PTm n) :
    (source f x M H Q).subst σ = source f (Syn.subst σ x) (Syn.subst σ M) (Syn.subst σ H) (Syn.subst σ Q) := by
  simp [source,one]

theorem shift_sources (f : PR 2) (x M H Q : PTm n) (h : Γ ⊢[PRAAx] source f x M H Q) :
    Γ ⊢[PRAAx] shiftSource f x M (radiusNumerator H) Q ⋏ shiftSource f x M (negativeStep H) Q := by
  let C := num 4*M
  have hQ := h.andE₂.andE₂.andE₁
  have hC : Γ ⊢[PRAAx] le one C :=
    positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring)) h.andE₁.andE₂.andE₁
  have fit : Γ ⊢[PRAAx] le (H*C) (one*Q) :=
    le_congr (mul_comm _ _) (one_mul Q).eqSymm h.andE₂.andE₂.andE₂
  have pos := GaussianDominantPairAlgebra.radius_bounded H Q hQ
  let z := negativeStep H
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq z ≐ H*H := by
    change Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.neg (radiusNumerator H)) ≐ H*H
    exact (ComplexLogarithmRemainder.normSq_neg (Γ := Γ) (radiusNumerator H)).eqTrans (radius_numerator_norm H)
  have neg : Γ ⊢[PRAAx] bounded (ofGaussian z Q) H Q :=
    bounded_of_cleared _ _ _ _ _ hQ hQ (ofGaussian_represents z Q hQ)
      (le_congr (congrMul (.eqRefl _) norm).eqSymm (by ipra_ring) (le_refl _))
  exact .andI (.andI h.andE₁ (.andI hQ (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hQ hC fit pos)))
    (.andI h.andE₁ (.andI hQ (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hQ hC fit neg)))

theorem translated_sources (f : PR 2) (x M H Q : PTm n) (h : Γ ⊢[PRAAx] source f x M H Q) :
    Γ ⊢[PRAAx] baseSource (incrementF f) (incrementData x (radiusNumerator H) Q) (two*M) ⋏
      baseSource (incrementF f) (incrementData x (negativeStep H) Q) (two*M) :=
  .andI (GaussianNamedGammaIncrementInput.original_source f x M _ Q (shift_sources f x M H Q h).andE₁)
    (GaussianNamedGammaIncrementInput.original_source f x M _ Q (shift_sources f x M H Q h).andE₂)

theorem frozen_source (f : PR 2) (k x M H Q : PTm n) (h : Γ ⊢[PRAAx] source f x M H Q)
    (hk : Γ ⊢[PRAAx] le (threshold M) k) :
    let q := ap2 f k x
    Γ ⊢[PRAAx] rationalSource (realNumerator q) (denominator q) (radius (realNumerator q) zero) (two*M) H Q := by
  have cert := GaussianNamedRightHalfPlaneSigned.actual_late f x M k h.andE₁ hk
  have hK := positive_product two M (le_succ_self one) h.andE₁.andE₂.andE₁
  exact .andI (projected_source _ _ _ cert) (.andI (.andI hK cert.andE₂.andE₁)
    (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁
      (le_congr (by ipra_ring) (.eqRefl _) h.andE₂.andE₂.andE₂))))

private theorem real_value (q : PTm n) (h : Γ ⊢[PRAAx] le one (realNumerator q)) :
    Γ ⊢[PRAAx] ZT.eq (real (rawGaussian q)) (ZT.ofNat (realNumerator q)) := by
  apply ZT.derive
  simpa only [native, ComplexLogarithmRemainder.eval_re_code] using
    (GaussianRootAlgebra.equal_re (native_value q h)).symm

private theorem translated_real (q r h Q Y : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (hr : Γ ⊢[PRAAx] r ≐ GaussianRationalHorner.qadd q (ofGaussian h Q))
    (hp : Γ ⊢[PRAAx] le one (realNumerator r))
    (hNum : Γ ⊢[PRAAx] ZT.eq
      (real (GaussianEulerParameterExponentialIncrement.shifted (rawGaussian q) (denominator q) h Q)) (ZT.ofNat Y)) :
    Γ ⊢[PRAAx] (realNumerator r)*(denominator q*Q) ≐ Y*denominator r := by
  let E := denominator q*Q
  have old := (GaussianNamedGammaIncrementInput.sum_represents q h Q hQ).andE₁
  have first := scalar_congr (.eqRefl _) (real_value r hp) (.eqRefl _) (raw_represents r).andE₁
  have second := scalar_congr (congrFst hr).eqSymm hNum (.eqRefl _) old
  have exactEq := ZT.toZ_eq (scalar_representation_cross (fstT r) _ _ (denominator r) E first second)
  apply deriveNat
  simp only [ZT.toZ_mul, ZT.toZ_ofNat] at exactEq
  dsimp only [E] at exactEq
  ipra_simps
  exact exactEq

theorem shifted_charts (f : PR 2) (k x M j H Q : PTm n) (hs : Γ ⊢[PRAAx] source f x M H Q)
    (hk : Γ ⊢[PRAAx] le (threshold (two*M)) k)
    (ht : Γ ⊢[PRAAx] le (threshold M) (shiftClock k)) :
    let q := ap2 f (shiftClock k) x
    let X := realNumerator q
    let D := denominator q
    let a := ap2 (incrementF f) k (incrementData x (radiusNumerator H) Q)
    let b := ap2 (incrementF f) k (incrementData x (negativeStep H) Q)
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (pointData j a) (data j (X*Q+H*D) (D*Q) (upperRadius X D H Q)) ⋏
      crossEquivalent nameF nameF (pointData j b) (lowerData j X D H Q) := by
  let q := ap2 f (shiftClock k) x
  let X := realNumerator q
  let D := denominator q
  let R := radius X zero
  let A := X*Q+H*D
  let Y := lowerNumerator X D H Q
  let u := incrementData x (radiusNumerator H) Q
  let v := incrementData x (negativeStep H) Q
  let a := ap2 (incrementF f) k u
  let b := ap2 (incrementF f) k v
  have hQ := hs.andE₂.andE₂.andE₁
  have h := frozen_source f (shiftClock k) x M H Q hs ht
  have cert := GaussianNamedRightHalfPlaneSigned.actual_late f x M (shiftClock k) hs.andE₁ ht
  have hypA := (translated_sources f x M H Q hs).andE₁
  have hypB := (translated_sources f x M H Q hs).andE₂
  have ca := GaussianNamedRightHalfPlaneSigned.actual_late (incrementF f) u (two*M) k hypA hk
  have cb := GaussianNamedRightHalfPlaneSigned.actual_late (incrementF f) v (two*M) k hypB hk
  have realEq := ZT.toZ_eq (real_value q cert.andE₁.andE₁.andE₁.andE₁)
  have clearA : Γ ⊢[PRAAx] ZT.eq
      (real (GaussianEulerParameterExponentialIncrement.shifted (rawGaussian q) D (radiusNumerator H) Q)) (ZT.ofNat A) := by
    apply ZT.derive
    simp only [GaussianEulerParameterExponentialIncrement.shifted, GaussianRootAlgebra.re_add, GaussianRootAlgebra.re_scale,
      ZT.toZ_ofNat, radiusNumerator, ComplexLogarithmRemainder.eval_re_code, realEq]
    dsimp only [A]
    ipra_simps
    ring
  have clearB : Γ ⊢[PRAAx] ZT.eq
      (real (GaussianEulerParameterExponentialIncrement.shifted (rawGaussian q) D (negativeStep H) Q)) (ZT.ofNat Y) := by
    have eq := natEq (window_geometry X D R (two*M) H Q h).andE₁
    apply ZT.derive
    simp only [GaussianEulerParameterExponentialIncrement.shifted, GaussianRootAlgebra.re_add, GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.re_neg, ZT.toZ_ofNat, negativeStep, radiusNumerator,
      ComplexLogarithmRemainder.eval_re_code, realEq]
    ipra_simps
    linear_combination -eq
  have eqA := translated_real q a (radiusNumerator H) Q A hQ (sample_at f k x _ Q) ca.andE₁.andE₁.andE₁.andE₁ clearA
  have eqB := translated_real q b (negativeStep H) Q Y hQ (sample_at f k x _ Q) cb.andE₁.andE₁.andE₁.andE₁ clearB
  exact .andI
    (rational_proper j _ _ _ _ _ _ (projected_source _ _ _ ca) (upper_source X D R H Q h.andE₁ hQ) eqA)
    (rational_proper j _ _ _ _ _ _ (projected_source _ _ _ cb) (lower_source X D R (two*M) H Q h) eqB)

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamedShift
