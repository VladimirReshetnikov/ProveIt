import IPRADerivations.Analysis.Gamma.Digamma.GaussianLogGammaEulerNamedDigamma

/-!
# Agreement with the original signed-rational digamma encoding

The raw observation decoder may choose a different denominator and a
different sign bit at zero. On certified rational inputs its normalized
point is the same original value. The zero-distance case of the exact
C27 continuity modulus identifies the two original evaluator names.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedDigammaRational

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianLogGammaEulerDigammaContinuity (canonical_fraction_lipschitz)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerNamedDigamma (pointData rationalData rational_data_at rationalMap nameF data)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerSlopeContinuity (input coefficient)
open GaussianNameEquivalence (crossEquivalent cross_at subst_crossEquivalent)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianNamedRightHalfPlaneLift (clock)
open GaussianNamedRightHalfPlaneSigned (certificate point point_eq_raw realNumerator imagNumerator denominator sign)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian_canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "digammaF" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "digammaData" => GaussianLogGammaEulerDigammaFractionsCofinal.data

private theorem exact_of_zero_rate (F G : PR 2) (x y C : PTm n)
    (h : Γ ⊢[PRAAx] independentRate F G x y (C * zero) one) : Γ ⊢[PRAAx] crossEquivalent F G x y := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let p : PTm (n + 1 + 1) := var 1
  let q : PTm (n + 1 + 1) := var 0
  have hs : Δ ⊢[PRAAx] independentRate F G (s x) (s y) (s C * zero) one := by
    simpa [Δ, s, Fm.shift, Syn.shift, one] using h.shift.shift
  have raw := rate_at F G (s x) (s y) (s C * zero) one p q hs
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) raw

theorem signed_rational_agreement (A B D neg R K : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hc : Γ ⊢[PRAAx] certificate (argument A B D neg) R K) :
    Γ ⊢[PRAAx] crossEquivalent digammaF digammaF (ap1 rationalData (argument A B D neg)) (digammaData A B D neg) := by
  let z := argument A B D neg
  let M := K + D
  have hM : Γ ⊢[PRAAx] le one M := le_trans h.andE₂ (le_add_left D K)
  have left : Γ ⊢[PRAAx] le (denominator z) (M * realNumerator z) :=
    le_trans hc.andE₂.andE₁ (le_mul_mono (le_add_right K D) (le_refl _))
  have right : Γ ⊢[PRAAx] le D (M * A) :=
    le_trans (le_add_left D K) (le_congr (by dsimp only [M]; ipra_ring) (.eqRefl _)
      (le_mul_mono (le_refl M) h.andE₁.andE₁))
  have src : Γ ⊢[PRAAx] input (realNumerator z) (denominator z) (sign z) A D neg M :=
    .andI hc.andE₁.andE₁ (.andI h (.andI hM (.andI left right)))
  have e := point_eq_raw z hc.andE₁.andE₁.andE₁.andE₁ (ofGaussian_canonical (native A B neg) D h.andE₂)
  have near : Γ ⊢[PRAAx] distanceBounded (point z) z zero one :=
    distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero z one (le_refl one))
  have rate := canonical_fraction_lipschitz (realNumerator z) (imagNumerator z) (denominator z) (sign z)
    A B D neg M zero one src (le_refl one) near
  have cross := exact_of_zero_rate digammaF digammaF (pointData z) (digammaData A B D neg) (coefficient M) rate
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr digammaF digammaF (pointData z) (ap1 rationalData z)
    (digammaData A B D neg) (digammaData A B D neg) (rational_data_at z).eqSymm (.eqRefl _) cross

theorem actual_named_digamma_signed_rational_agreement_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 2) (var 3) ⟶ certificate (argument (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5) ⟶
        crossEquivalent digammaF digammaF (ap1 rationalData (argument (var 0) (var 1) (var 2) (var 3)))
          (digammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 6 (.impI (.impI (signed_rational_agreement _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

private theorem constant_sample (p z M R : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF constantF) p (data z M R) ≐ ap2 digammaF (succ p) (ap1 rationalData z) := by
  let t := clock rationalMap p M R
  exact (GaussianLogGammaEulerNamedDigamma.sample_at constantF p z M R).eqTrans
    (congrAp2 digammaF (.eqRefl _) (congrAp1 rationalData (constant_at t z)))

private theorem constant_agreement (z y M R : PTm n)
    (agree : Γ ⊢[PRAAx] crossEquivalent digammaF digammaF (ap1 rationalData z) y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF constantF) digammaF (data z M R) y := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let s (a : PTm n) := Syn.shift (Syn.shift a)
  let p : PTm (n + 2) := var 1
  let q : PTm (n + 2) := var 0
  have hs : Δ ⊢[PRAAx] crossEquivalent digammaF digammaF (ap1 rationalData (s z)) (s y) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,subst_crossEquivalent,subst_ap1] using agree.shift.shift
  have raw := cross_at digammaF digammaF (ap1 rationalData (s z)) (s y) (succ p) q hs
  let P := unit p
  let Q := unit q
  let V := unit (succ p)
  have grow : Δ ⊢[PRAAx] le P V := GaussianExponentialReference.unit_monotone (le_succ_self p)
  have guard : Δ ⊢[PRAAx] le ((V+Q)*(P*Q)) ((P+Q)*(V*Q)) := by
    ipra_le Groth.ι (IPRA.Q.mk Δ Q)^2 * sl grow
  have retimed := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive (succ p)) (unit_positive q))
    (positive_product _ _ (unit_positive p) (unit_positive q)) guard raw
  simpa only [crossEquivalent, GaussianNamedRightHalfPlaneLift.subst_data, Δ,s,Syn.shift,p,q] using
    distance_congr (constant_sample p (s z) (s M) (s R)).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) retimed

theorem signed_rational_name_agreement (A B D neg R K M : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (hc : Γ ⊢[PRAAx] certificate (argument A B D neg) R K) :
    Γ ⊢[PRAAx] crossEquivalent (nameF constantF) digammaF (data (argument A B D neg) M R) (digammaData A B D neg) :=
  constant_agreement (argument A B D neg) (digammaData A B D neg) M R (signed_rational_agreement A B D neg R K h hc)

theorem actual_named_digamma_constant_agreement_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 0) (var 2) (var 3) ⟶ certificate (argument (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5) ⟶
        crossEquivalent (nameF constantF) digammaF (data (argument (var 0) (var 1) (var 2) (var 3)) (var 6) (var 4))
          (digammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 7 (.impI (.impI (signed_rational_name_agreement _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

/-- Any late input observation suffices as the C27 argument to the requested
absolute error, independently of both returned observation precisions. -/
theorem late_rational_rate (f : PR 2) (s k x M R : PTm n)
    (h : Γ ⊢[PRAAx] GaussianLogGammaEulerNamedDigamma.source f x M R)
    (hk : Γ ⊢[PRAAx] le (clock rationalMap s M R) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) digammaF (data x M R) (ap1 rationalData (ap2 f k x)) one (unit s) :=
  GaussianNamedRightHalfPlaneLift.frozen_rate rationalMap f s k x M R h hk

theorem actual_named_digamma_late_rational_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (GaussianLogGammaEulerNamedDigamma.source f (var 0) (var 1) (var 2) ⟶
        le (clock rationalMap (var 3) (var 1) (var 2)) (var 4) ⟶
          independentRate (nameF f) digammaF (data (var 0) (var 1) (var 2))
            (ap1 rationalData (ap2 f (var 4) (var 0))) one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (late_rational_rate f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamedDigammaRational
