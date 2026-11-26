import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentNamed
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentStirling
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetFirstFormulaNamed
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaPositiveLower

/-!
# Zeroth original Binet moment of the positive real named Stirling remainder

Freeze both original named Binet evaluations at one sufficiently late
input observation. Its exact axis certification removes the imaginary
numerator. The rational zeroth moment identity and the named first
formula identify the same zeroth moment with the original remainder.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamedStirling

open_ipra
open LeanProofs.IPRA.Foundations.GapDecision (zabs_congr)
open GaussianBinetFirstFormulaDecay (laplaceData subst_laplaceData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianNamedRightHalfPlane (radius threshold)
open GaussianNamedRightHalfPlaneSigned (actual_late realNumerator imagNumerator denominator sign)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "source" => GaussianNamedGammaPositiveLower.source
local notation "N" => GaussianBinetLaplaceMomentNamed.nameF
local notation "nd" => GaussianBinetLaplaceMomentNamed.data
local notation "J" => GaussianBinetLaplaceNamed.nameF
local notation "jd" => GaussianBinetLaplaceNamed.data
local notation "M" => GaussianBinetLaplaceMomentImproper.nameF
local notation "U" => GaussianBinetLaplaceImproperName.nameF
local notation "S" => GaussianBinetFirstFormulaNamed.remainderF
local notation "sd" => GaussianBinetFirstFormulaNamed.remainderData

theorem frozen_axis (f : PR 2) (k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (threshold A) k) :
    Γ ⊢[PRAAx] crossEquivalent M U (GaussianBinetLaplaceMomentNamed.frozenData f k x zero)
      (GaussianBinetLaplaceNamed.pointData (ap2 f k x)) := by
  let q := ap2 f k x
  let X := realNumerator q
  let D := denominator q
  let b := imagNumerator q
  let neg := sign q
  let T := GaussianLogGammaEulerResidualRadius.radius X zero
  let F := GaussianStirlingGlobalBounds.remainderF
  let d := GaussianStirlingGlobalBounds.remainderData X D zero
  let C := GaussianBinetStirlingRemainder.nameF
  let c := GaussianBinetStirlingRemainder.data X zero D neg zero
  have cert := actual_late f x A k h.andE₁ hk
  have hSign := cert.andE₁.andE₁
  have hZero : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D zero :=
    .andI (.andI hSign.andE₁.andE₁ (.orI₁ (.eqRefl zero))) hSign.andE₂
  have im : Γ ⊢[PRAAx] b ≐ zero :=
    (zabs_congr (ZT.toZ_eq (GaussianNamedGammaPositiveLower.decoded_imaginary_zero f k x h.andE₂))).eqTrans
      (GaussianL1.abs_ofNat zero)
  have dataEq : Γ ⊢[PRAAx] laplaceData X zero D neg ≐ GaussianBinetLaplaceNamed.pointData q := by
    simpa only [GaussianBinetLaplaceNamed.pointData,X,D,b,neg,subst_laplaceData,Syn.inst_zero,Syn.subst_inst_shift,
      Syn.subst_var] using
      Prf.eqCongr1 (laplaceData (Syn.shift X) (var 0) (Syn.shift D) (Syn.shift neg)) im.eqSymm
  have first := GaussianBinetLaplaceMomentStirling.stirling_equivalent X D zero hZero
  have axis := GaussianBinetStirlingRemainder.axis_equivalent X D neg zero hSign
  have integral := GaussianBinetFirstFormula.equivalent X zero D neg zero hSign
  have exact := GaussianGammaCompactCutoffAlignment.cross_data_congr C U c c
    (laplaceData X zero D neg) (GaussianBinetLaplaceNamed.pointData q) (.eqRefl _) dataEq integral
  exact cross_trans M F U (GaussianBinetLaplaceMomentImproper.data zero X D T) d _
    (cross_symm F M _ _ first) (cross_trans F C U d c _ (cross_symm C F _ _ axis) exact)

theorem observations (f : PR 2) (p x A R : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hR : Γ ⊢[PRAAx] le (radius f x) R) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (N f) p (nd x A zero)) (ap2 (J f) p (jd x A R)) (num 4) (unit p) := by
  let r := GaussianBinetLaplaceMomentNamed.clock p A zero
  let s := GaussianBinetLaplaceNamed.clock p A R
  let k := r+s
  let y := GaussianBinetLaplaceMomentNamed.frozenData f k x zero
  let z := GaussianBinetLaplaceNamed.pointData (ap2 f k x)
  have hp := unit_positive (Γ := Γ) p
  have left := GaussianBinetLaplaceMomentNamed.frozen_rate f p k x A zero h.andE₁ (le_add_right r s)
  have right := GaussianBinetLaplaceNamed.late_rational_rate f p k x A R (.andI h.andE₁ hR) (le_add_left s r)
  have eq := frozen_axis f k x A h (le_trans (GaussianBinetLaplaceMomentNamed.clock_margin p A zero) (le_add_right r s))
  have lifted := GaussianNamedRateTransport.transport (N f) M (N f) U (nd x A zero) y (nd x A zero) z one (unit p) hp left
    (cross_refl _ _ (GaussianBinetLaplaceMomentNamed.name_regular f x A zero h.andE₁)) (cross_symm _ _ _ _ eq)
  have sum := GaussianNamedRateComposition.same_denominator_at (N f) U (J f) (nd x A zero) z (jd x A R)
    one (unit p) one p p hp lifted
    (GaussianNamedRateComposition.symmetric (J f) U (jd x A R) z one (unit p) hp right)
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hp) hp
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)) sum

theorem laplace_equivalent (f : PR 2) (x A R : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hR : Γ ⊢[PRAAx] le (radius f x) R) : Γ ⊢[PRAAx]
    crossEquivalent (N f) (J f) (nd x A zero) (jd x A R) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 4)
    (GaussianBinetLaplaceMomentNamed.name_regular f x A zero h.andE₁)
    (GaussianBinetLaplaceNamed.name_regular f x A R (.andI h.andE₁ hR))
  refine .allI ?_
  let s (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (s x) (s A) := by
    simpa only [s,Fm.shift,Syn.shift,GaussianNamedGammaPositiveLower.subst_source] using h.shift
  have hr : Γ.map Fm.shift ⊢[PRAAx] le (radius f (s x)) (s R) := by
    simpa only [s,Fm.shift,Syn.shift,subst_le,GaussianNamedRightHalfPlane.subst_radius] using hR.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,s,GaussianBinetLaplaceMomentNamed.subst_data,
    GaussianNamedRightHalfPlaneLift.subst_data,LeanProofs.IPRA.PTm.subst_num,ConciseIPRA.PTm.subst_zero] using
    observations f (var 0) (s x) (s A) (s R) hs hr

theorem stirling_equivalent (f : PR 2) (x A R w : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hR : Γ ⊢[PRAAx] le (radius f x) R) : Γ ⊢[PRAAx]
    crossEquivalent (S f) (N f) (sd f x A R w) (nd x A zero) :=
  cross_trans _ _ _ _ _ _ (GaussianBinetFirstFormulaNamed.equivalent f x A R w (.andI h.andE₁ hR))
    (cross_symm _ _ _ _ (laplace_equivalent f x A R h hR))

theorem actual_named_zeroth_Binet_moment_Stirling_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 1) ⟶ le (radius f (var 0)) (var 2) ⟶
        crossEquivalent (S f) (N f) (sd f (var 0) (var 1) (var 2) (var 3)) (nd (var 0) (var 1) zero)) :=
  closeUniv 4 (.impI (.impI (stirling_equivalent f _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentNamedStirling
