import IPRADerivations.Analysis.GaussianLogGammaEulerDigammaPositiveAxis
import IPRADerivations.Analysis.GaussianLogGammaEulerNamedDigammaRational
import IPRADerivations.Analysis.GaussianNamedRightHalfPlaneConstant
import IPRADerivations.Analysis.GaussianGammaPositiveNamedDigammaFrozen

/-!
# The C27 evaluator on positive real names

The named C27 evaluator and the original Gamma-derivative quotient can
both be compared to the same late, exactly positive rational observation.
The rational-axis identity therefore extends to the complete original
domain of positive real names.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedDigammaPositiveAxis

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaMinimumFreezeRational (numerator denominator fraction_at frozen_rational_domain)
open GaussianGammaPositiveNamedDigammaFrozen (gain frozenData subst_gain)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerNamedDigamma (rationalMap rationalData name_regular)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedRightHalfPlane (radius subst_radius)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "origSource" => GaussianNamedPositiveDigamma.source
local notation "namedF" => GaussianLogGammaEulerNamedDigamma.nameF
local notation "namedData" => GaussianLogGammaEulerNamedDigamma.data
local notation "oldF" => GaussianNamedPositiveDigamma.nameF
local notation "oldData" => GaussianNamedPositiveDigamma.data
local notation "oldClock" => GaussianGammaPositiveNamedRationalFreeze.clock
local notation "rationalF" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "nativeF" => GaussianGammaDigammaNative.nameF

theorem named_chart (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] origSource f x A) :
    Γ ⊢[PRAAx] GaussianLogGammaEulerNamedDigamma.source f x A (radius f x) :=
  .andI h.andE₁ (le_refl _)

theorem frozen_cross (f : PR 2) (k x A : PTm n) (h : Γ ⊢[PRAAx] origSource f x A)
    (hk : Γ ⊢[PRAAx] le (GaussianNamedRightHalfPlane.threshold A) k) :
    Γ ⊢[PRAAx] crossEquivalent rationalF nativeF (ap1 rationalData (ap2 f k x)) (frozenData f k x) := by
  let a := numerator f k x
  let b := denominator f k x
  let z := argument a zero b zero
  let d := GaussianLogGammaEulerDigammaFractionsCofinal.data a zero b zero
  have hsrc := (frozen_rational_domain f k x A h hk).andE₁
  have hR : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source a b zero :=
    .andI (.andI hsrc.andE₁ (.orI₁ (.eqRefl _))) hsrc.andE₂
  have hz : Γ ⊢[PRAAx] z ≐ GaussianPositiveRationalLogarithm.fraction a b :=
    GaussianGammaFiniteValueProperness.fraction_equal (native a zero zero) (scale a oneCode) b hsrc.andE₂
      (GaussianLogGammaEulerPositiveAxis.native_axis_equal a zero (.orI₁ (.eqRefl _)))
  have enc := (fraction_at f k x A h hk).eqTrans hz.eqSymm
  have hc := GaussianNamedRightHalfPlaneConstant.signed_rational_certificate a zero b zero hR
  have src := GaussianLogGammaEulerNamedDigammaRational.signed_rational_agreement a zero b zero
    (radius constantF z) (two*b) hR hc
  have exactAxis := GaussianLogGammaEulerDigammaPositiveAxis.original_gamma_derivative_over_gamma a b hsrc
  have agree := cross_trans rationalF rationalF nativeF (ap1 rationalData z) d (frozenData f k x) src exactAxis
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr rationalF nativeF _ _ _ _
    (congrAp1 rationalData enc.eqSymm) (.eqRefl _) agree

def cost (f : PR 2) (x A : PTm n) : PTm n := one + gain f x A + two

@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x A : PTm n) :
    Syn.subst σ (cost f x A) = cost f (Syn.subst σ x) (Syn.subst σ A) := by
  simp only [cost, subst_gain, PTm.subst_add, one, two, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem diagonal (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] origSource f x A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (namedF f) p (namedData x A (radius f x)))
      (ap2 (oldF f) p (oldData f x A)) (cost f x A) (unit p) := by
  let R := radius f x
  let v := namedData x A R
  let w := oldData f x A
  let s := GaussianNamedRightHalfPlaneLift.clock rationalMap p A R
  let t := oldClock f p one x A
  let k := s+t
  let y := ap1 rationalData (ap2 f k x)
  let z := frozenData f k x
  let G := gain f x A
  let U := unit p
  have hlate := le_trans (GaussianGammaPositiveNamedRationalFreeze.threshold_le (Γ := Γ) f p one x A) (le_add_left t s)
  have hu := unit_positive (Γ := Γ) p
  have newRate := GaussianLogGammaEulerNamedDigammaRational.late_rational_rate f p k x A R (named_chart f x A h)
    (le_add_right s t)
  have oldRate := GaussianGammaPositiveNamedDigammaFrozen.original_rate f p k x A h (le_add_left t s)
  have equal := frozen_cross f k x A h hlate
  have shifted := GaussianNamedRateTransport.transport (namedF f) rationalF (namedF f) nativeF v y v z one U hu newRate
    (cross_refl _ _ (name_regular f x A R (named_chart f x A h))) (cross_symm _ _ _ _ equal)
  have raw := GaussianNamedRateComposition.same_denominator_at (namedF f) nativeF (oldF f) v z w one U G p p hu shifted
    (GaussianNamedRateComposition.symmetric (oldF f) nativeF w z G U hu oldRate)
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive U p p hu) hu
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,cost,G,U]; ipra_ring)) raw

theorem original_gamma_derivative_over_gamma (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] origSource f x A) :
    Γ ⊢[PRAAx] crossEquivalent (namedF f) (oldF f) (namedData x A (radius f x)) (oldData f x A) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] origSource f (Syn.shift x) (Syn.shift A) := by
    simpa only [Fm.shift, GaussianNamedGammaPositiveLower.subst_source, Syn.shift] using h.shift
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost f x A)
    (name_regular f x A _ (named_chart f x A h)) (GaussianNamedPositiveDigamma.name_regular f x A h) (.allI ?_)
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, subst_cost, subst_radius,
    GaussianNamedRightHalfPlaneLift.subst_data, GaussianNamedPositiveDigamma.subst_data] using
    diagonal f (var 0) (Syn.shift x) (Syn.shift A) hs

theorem actual_named_complex_digamma_positive_axis_is_original_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (origSource f (var 0) (var 1) ⟶ crossEquivalent (namedF f) (oldF f)
        (namedData (var 0) (var 1) (radius f (var 0))) (oldData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_gamma_derivative_over_gamma f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedDigammaPositiveAxis
