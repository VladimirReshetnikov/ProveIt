import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeAtOne
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeFormula

/-!
# The integral of log-Gamma shifted by one on the unit interval

A tag `i/N` in the unit interval is read by the original real
log-Gamma at `(N+i)/N`. The checked positive Raabe quadrature at
the unit argument uses these exact tags and names the Stirling
constant minus the exact rational unit.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeShiftedUnitFormula

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid quadrature sampleBody sampleData sample_body_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedDifference (name_regular)
open GaussianRaabeCofinalSchedule (clockFor count)
open GaussianRaabeStirlingRemainder (constantSample)
open GaussianRaabeUnitGridRecurrence (logGammaEvaluator log_gamma_at)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSyntheticDivision (qone qsub_congr)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => GaussianStirlingConstant.nameF
local notation "cd" => GaussianStirlingConstant.nameData
local notation "F" => GaussianRaabeRightSide.nameF
local notation "fd" => GaussianRaabeRightSide.data

abbrev nameF : PR 2 := GaussianRaabeFormula.nameF
def data : PTm n := GaussianRaabeFormula.data one one

def targetF : PR 2 := GaussianNamedDifference.nameF C constantF
def targetData (w : PTm n) : PTm n := GaussianNamedDifference.data (cd w) qone

ipra_subst targetData

theorem tag_at (i p N : PTm n) :
    Γ ⊢[PRAAx] inst2 (sampleBody logGammaEvaluator) i (sampleData p N one one one zero) ≐
      ap2 logGammaF p (logGammaData (N+i) N) := by
  have tag : Γ ⊢[PRAAx] grid i N one one one ≐ pairT (N+i) N :=
    congrPairT (by ipra_ring) (one_mul N)
  exact (sample_body_at logGammaEvaluator i p N one one one zero).eqTrans
    ((congrAp3 logGammaEvaluator (.eqRefl p) tag (.eqRefl zero)).eqTrans (log_gamma_at p (N+i) N zero))

theorem sample_at (p : PTm n) :
    let h := p+num 4
    let N := count h one one
    Γ ⊢[PRAAx] ap2 nameF p data ≐ quadrature logGammaEvaluator (clockFor h N one one) N one one one zero :=
  GaussianRaabeFormula.sample_at p one one

theorem regular : Γ ⊢[PRAAx] pointCN nameF data :=
  GaussianRaabeFormula.regular one one (.andI (le_refl one) (le_refl one))

theorem target_regular (w : PTm n) : Γ ⊢[PRAAx] pointCN targetF (targetData w) :=
  name_regular C constantF (cd w) qone (GaussianStirlingConstant.name_regular w) (constant_regular qone)

theorem target_sample_error (p w : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 targetF p (targetData w)) (qsub (constantSample p w) qone)
      (num 6) (unit p) :=
  distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p qone)) (.eqRefl _) (.eqRefl _)
    (GaussianNamedDifference.sample_error C constantF (cd w) qone p
      (GaussianStirlingConstant.name_regular w) (constant_regular qone))

private theorem right_sample_error (p w : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p (fd one one w)) (ap2 targetF p (targetData w))
      (num 27) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have original := GaussianRaabeAtOne.right_side_at_unit (Γ := Γ) p one w (le_refl one)
  have named := distance_symmetric _ _ _ _ hp (target_sample_error p w)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianRaabeRightSide.cost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp original named)

theorem right_side_equivalent (w : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent F targetF (fd one one w) (targetData w) := by
  have hr := GaussianRaabeRightSide.regular (Γ := Γ) one one w (.andI (le_refl one) (le_refl one))
  apply GaussianNameRingLaws.equivalent_of_envelope F targetF (fd one one w) (targetData w)
    (num 27) hr (target_regular w)
  refine .allI ?_
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,
    GaussianRaabeRightSide.subst_data,subst_targetData,one,ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ,LeanProofs.IPRA.PTm.subst_num] using
    right_sample_error (Γ := Γ.map Fm.shift) (var 0) (Syn.shift w)

theorem equivalent (w : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent nameF targetF data (targetData w) :=
  cross_trans nameF F targetF data (fd one one w) (targetData w)
    (GaussianRaabeFormula.equivalent one one w (.andI (le_refl one) (le_refl one))) (right_side_equivalent w)

theorem actual_log_Gamma_shifted_unit_integral_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent nameF targetF data (targetData (var 0))) :=
  closeUniv 1 (equivalent _)

end LeanProofs.IPRA.Analysis.GaussianRaabeShiftedUnitFormula
