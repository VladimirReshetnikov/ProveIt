import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.FrozenInputs.GaussianGammaMinimumFreezeRational
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.RationalCharts.GaussianLogGammaEulerChartAgreement
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.NamedValues.GaussianLogGammaEulerNamed
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.NamedValues.GaussianLogGammaEulerPositiveAxis

/-!
# The named Euler log-Gamma on the positive real axis

Freeze both named evaluators at the same sufficiently late rational
observation. The positive rational identity applies to that observation
in the old fraction encoding, and chart agreement identifies the new
evaluator's signed-rational decoding with that fraction.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedPositiveAxis

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaMinimumFreezeRational (numerator denominator fraction_at frozen_rational_domain frozen_log_rate)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerNamed (rationalMap rationalData rational_data_at name_regular)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianNamedRightHalfPlane (radius threshold subst_radius)
open GaussianNamedRightHalfPlaneSigned
  (actual_late point point_eq_raw realNumerator imagNumerator sign)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (canonical_congr ofGaussian_canonical)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm (gammaLogMargin logGammaF logGammaData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "source" => GaussianNamedGammaPositiveLower.source
local notation "namedF" => GaussianLogGammaEulerNamed.nameF
local notation "namedData" => GaussianLogGammaEulerNamed.data
local notation "oldF" => GaussianGammaMinimumFreeze.nameF
local notation "oldData" => GaussianGammaMinimumFreeze.data
local notation "cofinalF" => GaussianLogGammaEulerCofinal.nameF
local notation "cofinalData" => GaussianLogGammaEulerCofinal.canonicalData

theorem frozen_cross (f : PR 2) (k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (threshold A) k) :
    Γ ⊢[PRAAx] crossEquivalent cofinalF logGammaF (ap1 rationalData (ap2 f k x))
      (logGammaData (numerator f k x) (denominator f k x)) := by
  let q := ap2 f k x
  let a := numerator f k x
  let b := denominator f k x
  let z := argument a zero b zero
  let d := GaussianLogGammaEulerNamed.pointData q
  let c := cofinalData a zero b zero
  let r := logGammaData a b
  have hsrc := (frozen_rational_domain f k x A h hk).andE₁
  have hr : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source a b zero :=
    .andI (.andI hsrc.andE₁ (.orI₁ (.eqRefl _))) hsrc.andE₂
  have hz : Γ ⊢[PRAAx] z ≐ GaussianPositiveRationalLogarithm.fraction a b :=
    GaussianGammaFiniteValueProperness.fraction_equal (native a zero zero) (scale a oneCode) b hsrc.andE₂
      (GaussianLogGammaEulerPositiveAxis.native_axis_equal a zero (.orI₁ (.eqRefl _)))
  have eq : Γ ⊢[PRAAx] q ≐ z := (fraction_at f k x A h hk).eqTrans hz.eqSymm
  have cert := actual_late f x A k h.andE₁ hk
  have hq := canonical_congr eq (ofGaussian_canonical (native a zero zero) b hsrc.andE₂)
  have bind : Γ ⊢[PRAAx] point q ≐ z := (point_eq_raw q cert.andE₁.andE₁.andE₁.andE₁ hq).eqTrans eq
  have charts := GaussianLogGammaEulerChartAgreement.canonical_agreement (realNumerator q) (imagNumerator q)
    (GaussianNamedRightHalfPlaneSigned.denominator q) (sign q) a zero b zero cert.andE₁.andE₁ hr bind
  have axis := GaussianLogGammaEulerPositiveAxis.equivalent a b zero hr
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr cofinalF logGammaF d (ap1 rationalData q) r r
    (rational_data_at q).eqSymm (.eqRefl _) (cross_trans cofinalF cofinalF logGammaF d c r charts axis)

def cost : PTm n := one + gammaLogMargin + two

private theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) : Syn.subst σ (cost : PTm n) = (cost : PTm m) := by
  simp [cost, gammaLogMargin, GaussianStirlingGammaLogarithm.gammaMargin, one, two]

theorem diagonal (f : PR 2) (p x A R : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hR : Γ ⊢[PRAAx] le (radius f x) R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (namedF f) p (namedData x A R)) (ap2 (oldF f) p (oldData x A)) (cost : PTm n) (unit p) := by
  let s := GaussianNamedRightHalfPlaneLift.clock rationalMap p A R
  let t := GaussianNamedGammaPositiveLower.clock f p x A
  let k := s+t
  let u := namedData x A R
  let v := oldData x A
  let y := ap1 rationalData (ap2 f k x)
  let z := logGammaData (numerator f k x) (denominator f k x)
  let U := unit p
  let G := (gammaLogMargin : PTm n)
  have late : Γ ⊢[PRAAx] le t k := le_add_left t s
  have hk := le_trans (le_add_right (Γ := Γ) (threshold A) _) late
  have hd := le_trans (le_add_left (Γ := Γ) _ (threshold A)) late
  have hu := unit_positive (Γ := Γ) p
  have src : Γ ⊢[PRAAx] GaussianLogGammaEulerNamed.source f x A R := .andI h.andE₁ hR
  have a := GaussianLogGammaEulerNamed.late_rational_rate f p k x A R src (le_add_right s t)
  have b := frozen_log_rate f p k x A h hk hd
  have link := frozen_cross f k x A h hk
  have moved := GaussianNamedRateTransport.transport (namedF f) cofinalF (namedF f) logGammaF u y u z one U hu a
    (cross_refl _ _ (name_regular f x A R src)) (cross_symm _ _ _ _ link)
  have joined := GaussianNamedRateComposition.same_denominator_at (namedF f) logGammaF (oldF f) u z v one U G p p hu moved
    (GaussianNamedRateComposition.symmetric (oldF f) logGammaF v z G U hu b)
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive U p p hu) hu
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,cost,G,U]; ipra_ring)) joined

theorem equivalent_at_radius (f : PR 2) (x A R : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hR : Γ ⊢[PRAAx] le (radius f x) R) : Γ ⊢[PRAAx]
    crossEquivalent (namedF f) (oldF f) (namedData x A R) (oldData x A) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift A) := by
    simpa only [Fm.shift, GaussianNamedGammaPositiveLower.subst_source, Syn.shift] using h.shift
  have hr : Γ.map Fm.shift ⊢[PRAAx] le (radius f (Syn.shift x)) (Syn.shift R) := by
    simpa only [Fm.shift, Syn.shift, subst_le, subst_radius] using hR.shift
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost : PTm n)
    (name_regular f x A R (.andI h.andE₁ hR)) (GaussianGammaMinimumFreeze.name_regular f x A h) (.allI ?_)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, subst_cost,
    GaussianNamedRightHalfPlaneLift.subst_data, GaussianGammaMinimumFreeze.subst_data] using
    diagonal f (var 0) (Syn.shift x) (Syn.shift A) (Syn.shift R) hs hr

theorem equivalent (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    crossEquivalent (namedF f) (oldF f) (namedData x A (radius f x)) (oldData x A) :=
  equivalent_at_radius f x A (radius f x) h (le_refl _)

theorem actual_named_complex_log_Gamma_positive_axis_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ crossEquivalent (namedF f) (oldF f)
        (namedData (var 0) (var 1) (radius f (var 0))) (oldData (var 0) (var 1))) :=
  closeUniv 2 (.impI (equivalent f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedPositiveAxis
