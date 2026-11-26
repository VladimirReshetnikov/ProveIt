import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootMembershipHit
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSlackRemoval

/-!
# Exact represented root-support membership and the sampled root equation

Member is the source formula forall k exists t>=k, D_t(z)<=2^(-k), using
the actual Euclidean distance-name cut. The forward implication uses the
source's computed stage and sample precision. The converse eliminates the
existential stage locally, derives every finite dyadic residual slack, and
removes that slack by ordinary rational arithmetic. No represented nearest
root, root separation, unbounded search or limit principle is supplied.

The zero predicate is the source's explicit normalized V_s root equation.
Its interpretation by an actual fast polynomial-value name and the two
sharp represented evaluation/distance estimates are separate developments.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootMembership

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (R CN unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRootRadius (roots)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN distanceLE)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (T pointBounds normalizedZero stageIndex sampleIndex targetDenominator)
open LeanProofs.IPRA.Analysis.GaussianRootMembershipHit (residual slack)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inputContract (step a : PR 3) (point : PR 2) (N U x : PTm n) : Fm PTm n :=
  monicRD step ⋏ (CN a N x ⋏ (le one N ⋏ (le (R a N x) U ⋏ (pointCN point x ⋏ pointBounds point U x))))
def stageCondition (step a : PR 3) (point : PR 2) (N x k t : PTm n) : Fm PTm n :=
  le k t ⋏ distanceLE point (roots step a N t x) x one (unit k)
def atPrecision (step a : PR 3) (point : PR 2) (N x k : PTm n) : Fm PTm n :=
  .ex (stageCondition step a point (Syn.shift N) (Syn.shift x) (Syn.shift k) (var 0))
def member (step a : PR 3) (point : PR 2) (N x : PTm n) : Fm PTm n :=
  .all (atPrecision step a point (Syn.shift N) (Syn.shift x) (var 0))

@[simp] theorem subst_inputContract {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (point : PR 2) (N U x : PTm n) :
    (inputContract step a point N U x).subst σ = inputContract step a point (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) := by simp [inputContract]
@[simp] theorem subst_stageCondition {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (point : PR 2) (N x k t : PTm n) :
    (stageCondition step a point N x k t).subst σ = stageCondition step a point
      (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ k) (Syn.subst σ t) := by simp [stageCondition]
@[simp] theorem subst_atPrecision {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (point : PR 2) (N x k : PTm n) :
    (atPrecision step a point N x k).subst σ = atPrecision step a point (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ k) := by
  simp [atPrecision,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_member {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (point : PR 2) (N x : PTm n) :
    (member step a point N x).subst σ = member step a point (Syn.subst σ N) (Syn.subst σ x) := by
  simp [member,Syn.subst_shift,Syn.shift_subst]

theorem member_at (step a : PR 3) (point : PR 2) (N x k : PTm n)
    (h : Γ ⊢[PRAAx] member step a point N x) : Γ ⊢[PRAAx] atPrecision step a point N x k := by
  simpa only [member,subst_atPrecision,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE k

theorem precision_intro (step a : PR 3) (point : PR 2) (N x k t : PTm n)
    (h : Γ ⊢[PRAAx] stageCondition step a point N x k t) : Γ ⊢[PRAAx] atPrecision step a point N x k := by
  refine .exI t ?_
  simpa only [subst_stageCondition,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h

theorem root_to_stage (step a : PR 3) (point : PR 2) (N U x k : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N U x)
    (hZero : Γ ⊢[PRAAx] normalizedZero a point N U x) : Γ ⊢[PRAAx]
    stageCondition step a point N x k (stageIndex N U k) := by
  have rd := Prf.andE₁ h
  have cn := Prf.andE₁ (Prf.andE₂ h)
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have ru := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have pointData := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have hu := le_trans (GaussianRootSupport.radius_positive a N x) ru
  have found := GaussianRootApproximationWitness.selected_certificate step a point N U x k rd cn hn hu (Prf.andE₂ pointData) hZero
  have hit := GaussianRationalCover.hit_intro (GaussianRootApproximationWitness.query point a N U x k)
    (GaussianRootApproximationWitness.rootList step a N U x k) one (targetDenominator k)
    (GaussianRootApproximationWitness.selected step a point N U x k) (Prf.andE₁ found) (Prf.andE₂ found)
  have budget : Γ ⊢[PRAAx] le ((one*unit (sampleIndex a N U x k)+targetDenominator k)*unit k)
      (one*(targetDenominator k*unit (sampleIndex a N U x k))) :=
    le_congr (by unfold targetDenominator unit; ipra_ring) (by unfold targetDenominator unit; ipra_ring)
      (GaussianRootMembershipBudget.forward_point_error_budget k (sampleIndex a N U x k)
        (GaussianRootAdequacySchedule.sample_ge_succ _ _ _ _))
  exact .andI (GaussianRootAdequacySchedule.stage_ge_index _ _)
    (GaussianEuclideanDistanceName.finite_hit_to_cut point (roots step a N (stageIndex N U k) x) x
      (sampleIndex a N U x k) one (targetDenominator k) one (unit k) (Prf.andE₁ pointData)
      (GaussianRootApproximationWitness.target_denominator_positive k) (unit_positive k) hit budget)

theorem zero_to_member (step a : PR 3) (point : PR 2) (N U x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N U x)
    (hZero : Γ ⊢[PRAAx] normalizedZero a point N U x) : Γ ⊢[PRAAx] member step a point N x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inputContract,Syn.shift] using h.shift
  have hz : Γ.map Fm.shift ⊢[PRAAx] normalizedZero a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRootApproximationWitness.subst_normalizedZero,Syn.shift] using hZero.shift
  exact precision_intro _ _ _ _ _ _ _ (root_to_stage step a point (Syn.shift N) (Syn.shift U) (Syn.shift x) (var 0) hs hz)

theorem residual_from_stage (step a : PR 3) (point : PR 2) (N U t s m x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N U x)
    (hStage : Γ ⊢[PRAAx] stageCondition step a point N x m t) : Γ ⊢[PRAAx]
    bounded (residual a point N s x) (T a N U x*unit m+slack a N U x*unit s) (unit s*unit m) := by
  have rd := Prf.andE₁ h
  have cn := Prf.andE₁ (Prf.andE₂ h)
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have ru := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have pointData := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  exact GaussianRootMembershipHit.residual_from_cut step a point N U t s m x rd cn hn ru (Prf.andE₁ pointData)
    (GaussianRootApproximationWitness.point_at _ _ _ s (Prf.andE₂ pointData)) (Prf.andE₁ hStage) (Prf.andE₂ hStage)

/-- The membership witness is eliminated before producing a bound on the
fixed original V_s. Its existential stage never escapes into the result. -/
theorem member_residual_at (step a : PR 3) (point : PR 2) (N U x s m : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N U x)
    (hMember : Γ ⊢[PRAAx] member step a point N x) : Γ ⊢[PRAAx]
    bounded (residual a point N s x) (T a N U x*unit m+slack a N U x*unit s) (unit s*unit m) := by
  refine .exE (member_at step a point N x m hMember) ?_
  let E := stageCondition step a point (Syn.shift N) (Syn.shift x) (Syn.shift m) (var 0)
  have hs : E :: Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inputContract,Syn.shift] using h.shift.wk
  have result := residual_from_stage step a point (Syn.shift N) (Syn.shift U) (var 0) (Syn.shift s) (Syn.shift m) (Syn.shift x)
    hs (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)
  simpa only [E,Fm.shift,GaussianRationalMetric.subst_bounded,GaussianRootMembershipHit.subst_residual,
    GaussianRootApproximationWitness.subst_T,GaussianCoefficientNameBounds.subst_unit,
    GaussianRootMembershipHit.subst_slack,PTm.subst_add,PTm.subst_mul,Syn.shift] using result

theorem member_residual_slack (step a : PR 3) (point : PR 2) (N U x s : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N U x)
    (hMember : Γ ⊢[PRAAx] member step a point N x) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.allSlack (residual a point N s x) (T a N U x) (unit s) (slack a N U x) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inputContract,Syn.shift] using h.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] member step a point (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_member,Syn.shift] using hMember.shift
  simpa only [GaussianRationalSlackRemoval.slack,Syn.shift,GaussianRootMembershipHit.subst_residual,
    GaussianRootApproximationWitness.subst_T,GaussianCoefficientNameBounds.subst_unit,
    GaussianRootMembershipHit.subst_slack,unit,subst_ap2,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    member_residual_at step a point (Syn.shift N) (Syn.shift U) (Syn.shift x) (Syn.shift s) (var 0) hs hm

theorem member_residual_zero (step a : PR 3) (point : PR 2) (N U x s : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N U x)
    (hMember : Γ ⊢[PRAAx] member step a point N x) : Γ ⊢[PRAAx]
    bounded (residual a point N s x) (T a N U x) (unit s) :=
  GaussianRationalSlackRemoval.slack_removal _ _ _ _ (unit_positive s) (member_residual_slack _ _ _ _ _ _ _ h hMember)

theorem member_to_zero (step a : PR 3) (point : PR 2) (N U x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N U x)
    (hMember : Γ ⊢[PRAAx] member step a point N x) : Γ ⊢[PRAAx] normalizedZero a point N U x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inputContract,Syn.shift] using h.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] member step a point (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_member,Syn.shift] using hMember.shift
  exact member_residual_zero step a point (Syn.shift N) (Syn.shift U) (Syn.shift x) (var 0) hs hm

theorem membership_iff_zero (step a : PR 3) (point : PR 2) (N U x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N U x) : Γ ⊢[PRAAx]
    Fm.iff (member step a point N x) (normalizedZero a point N U x) :=
  .iffI (.impI (member_to_zero _ _ _ _ _ _ h.wk Prf.hyp0))
    (.impI (zero_to_member _ _ _ _ _ _ h.wk Prf.hyp0))

theorem source_member_iff_normalized_root_closed (step a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (inputContract step a point (var 0) (var 1) (var 2) ⟶
      Fm.iff (member step a point (var 0) (var 2)) (normalizedZero a point (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (membership_iff_zero _ _ _ _ _ _ Prf.hyp0))

theorem primitive_root_to_member_stage_closed (step a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract step a point (var 0) (var 1) (var 2) ⟶ normalizedZero a point (var 0) (var 1) (var 2) ⟶
      stageCondition step a point (var 0) (var 2) (var 3) (stageIndex (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (root_to_stage _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRootMembership
