import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootResidualFromHit
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootMembershipBudget

/-!
# A represented root-support cut gives a finite residual with dyadic slack

The original Euclidean distance cut at stage t≥m is instantiated at the
prescribed precision m. Its actual square-root observation supplies a
stored-point hit near point(m+2). Genuine point-name regularity transfers
that hit to point(s). The checked source residual estimate and the actual
stage denominator then give T·2^(-s)+(4M_U+2C_R)·2^(-m).
No desired residual, convergent value, or zero equation is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootMembershipHit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (A R CN unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRootRadius (roots)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName
  (pointCN point_cn_at distanceLE cut_to_hit hit_triangle hit_radius_mono)
open LeanProofs.IPRA.Analysis.GaussianRootMembershipBudget (slackCoefficient)
open LeanProofs.IPRA.Analysis.GaussianRootSchedule (four coefficientConstant)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def c (a : PR 3) (N x : PTm n) : PTm n := coefficientConstant N (R a N x)
def M (a : PR 3) (N U x : PTm n) : PTm n := GaussianRationalHornerLipschitz.constant N U (A a N x)
def slack (a : PR 3) (N U x : PTm n) : PTm n := slackCoefficient (c a N x) (M a N U x)
def residual (a : PR 3) (point : PR 2) (N s x : PTm n) : PTm n :=
  evaluate (GaussianRootSamples.sample a N s x) (ap2 point s x)

@[simp] theorem subst_c {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N x : PTm n) :
    Syn.subst σ (c a N x) = c a (Syn.subst σ N) (Syn.subst σ x) := by simp [c]
@[simp] theorem subst_M {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N U x : PTm n) :
    Syn.subst σ (M a N U x) = M a (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) := by simp [M]
@[simp] theorem subst_slack {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N U x : PTm n) :
    Syn.subst σ (slack a N U x) = slack a (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) := by simp [slack]
@[simp] theorem subst_residual {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2) (N s x : PTm n) :
    Syn.subst σ (residual a point N s x) = residual a point (Syn.subst σ N) (Syn.subst σ s) (Syn.subst σ x) := by simp [residual]

theorem residual_from_cut (step a : PR 3) (point : PR 2) (N U t s m x : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hRU : Γ ⊢[PRAAx] le (R a N x) U)
    (hPoint : Γ ⊢[PRAAx] pointCN point x) (hz : Γ ⊢[PRAAx] bounded (ap2 point s x) U one)
    (hmt : Γ ⊢[PRAAx] le m t)
    (hCut : Γ ⊢[PRAAx] distanceLE point (roots step a N t x) x one (unit m)) : Γ ⊢[PRAAx]
    bounded (residual a point N s x)
      (GaussianRootApproximationWitness.T a N U x*unit m+slack a N U x*unit s) (unit s*unit m) := by
  let d := unit s
  let h := unit m
  let K := unit (m+two)
  let L := roots step a N t x
  have dpos : Γ ⊢[PRAAx] le one d := unit_positive s
  have hpos : Γ ⊢[PRAAx] le one h := unit_positive m
  have kpos : Γ ⊢[PRAAx] le one K := unit_positive _
  have dhpos := positive_product _ _ dpos hpos
  have dkpos := positive_product _ _ dpos kpos
  have hhpos := positive_product _ _ hpos hpos
  have nonempty : Γ ⊢[PRAAx] le one (length L) :=
    le_congr (.eqRefl _) (GaussianRootRadius.roots_length step a N t x).eqSymm hN
  have hit := cut_to_hit point L x one h m nonempty hpos hCut
  have moved := hit_triangle (ap2 point s x) (ap2 point (m+two) x) L
    (d+K) (d*K) (one*h+two*h) (h*h) dkpos hhpos (point_cn_at point x s (m+two) hPoint) hit
  have sourcePos := positive_product _ _ dkpos hhpos
  have precisionOrder : Γ ⊢[PRAAx] le h K :=
    GaussianRootMembershipBudget.unit_monotone m (m+two) (le_add_right m two)
  have transfer : Γ ⊢[PRAAx] le (((d+K)*(h*h)+(one*h+two*h)*(d*K))*(d*h))
      ((h+four*d)*((d*K)*(h*h))) :=
    le_congr (by ipra_ring) (.eqRefl _) (GaussianRootMembershipBudget.cut_point_transfer_budget d h K precisionOrder)
  have finalHit := hit_radius_mono (ap2 point s x) L _ _ (h+four*d) (d*h) sourcePos dhpos transfer moved
  have raw := GaussianRootResidualFromHit.residual_from_hit step a N U t s x (ap2 point s x)
    (h+four*d) (d*h) hRD hCN hN hRU hz dhpos finalHit
  have upperC := GaussianRootMembershipBudget.coefficient_constant_monotone N (R a N x) U hRU
  have upperD := GaussianRootMembershipBudget.stage_denominator_lower N (R a N x) t m hN hmt
  have budget : Γ ⊢[PRAAx] le
      (GaussianRootResidualFromHit.numerator a N U t s x (h+four*d) (d*h)*(d*h))
      ((GaussianRootApproximationWitness.T a N U x*h+slack a N U x*d)*
        GaussianRootResidualFromHit.denominator a N t s x (d*h)) := by
    simpa only [GaussianRootResidualFromHit.numerator,GaussianRootResidualFromHit.denominator,
      GaussianRootFiniteEvaluation.coefficientNumerator,GaussianRootFiniteEvaluation.coefficientDenominator,
      GaussianRootFiniteEvaluation.denominator,GaussianRootApproximationWitness.T,GaussianRootApproximationWitness.C,
      slack,c,M] using
      GaussianRootMembershipBudget.converse_residual_budget (c a N x) (coefficientConstant N U)
        (M a N U x) d h (GaussianRootFiniteEvaluation.denominator a N t x) upperC upperD
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ dhpos (GaussianRootFiniteEvaluation.coefficient_denominator_positive a N t s x)) dhpos budget raw

theorem finite_member_residual_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (monicRD step ⟶ CN a (var 0) (var 5) ⟶ le one (var 0) ⟶ le (R a (var 0) (var 5)) (var 1) ⟶
      pointCN point (var 5) ⟶ bounded (ap2 point (var 3) (var 5)) (var 1) one ⟶ le (var 4) (var 2) ⟶
      distanceLE point (roots step a (var 0) (var 2) (var 5)) (var 5) one (unit (var 4)) ⟶
        bounded (residual a point (var 0) (var 3) (var 5))
          (GaussianRootApproximationWitness.T a (var 0) (var 1) (var 5)*unit (var 4)+
            slack a (var 0) (var 1) (var 5)*unit (var 3)) (unit (var 3)*unit (var 4))) := by
  apply closeUniv 6
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  exact residual_from_cut _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRootMembershipHit
