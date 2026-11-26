import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootMembership
import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceUpperCut
import IPRADerivations.Analysis.RationalArithmetic.GaussianScalarSlackRemoval
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootDistanceCompletion

/-!
# Zero of the actual completed root-distance name

Source04's unnumbered completion corollary is proved from the actual
Euclidean distance observations and the source root-support stage bounds.
The existential membership stage is eliminated locally before removing
finite scalar slack from a fixed rational query. The reverse implication
uses an explicit later diagonal stage, rather than an unbounded search.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootDistanceZero

open_ipra
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN distanceLE fraction)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def three : PTm n := succ two
def inputContract (step a : PR 3) (point : PR 2) (N x : PTm n) : Fm PTm n :=
  monicRD step ⋏ (CN a N x ⋏ (le one N ⋏ pointCN point x))

ipra_subst three
ipra_subst inputContract

/-- A later membership precision and a stage comparison yield two units
of fixed-query error plus three vanishing precision units. -/
theorem member_query_budget (B H L : PTm n) (hHL : Γ ⊢[PRAAx] le H L) : Γ ⊢[PRAAx]
    le (((H+L)*(B*H)+(two*H+B)*(L*H))*(B*H))
      ((two*H+three*B)*((L*H)*(B*H))) := by
  have gap := natEq (eq_add_of_le hHL)
  apply le_of_eq_add (d := B*B*H*H*PTm.monus L H)
  apply deriveNat
  unfold three
  ipra_simps
  rw [gap]
  ring

/-- Exact finite budget for turning a small square-root observation into
a represented cut at the earlier requested membership precision. -/
theorem zero_query_budget (u J K : PTm n) (hJ : Γ ⊢[PRAAx] J ≐ two*u)
    (hK : Γ ⊢[PRAAx] le (two*J) K) : Γ ⊢[PRAAx]
    le (((K+J)*K+J*K)*u) (one*((J*K)*K)) := by
  have j := natEq hJ
  have gap := natEq (eq_add_of_le hK)
  apply le_of_eq_add (d := u*K*PTm.monus K (two*J))
  apply deriveNat
  ipra_simps
  rw [gap,j]
  ring

def completedZero (step a : PR 3) (point : PR 2) (N x : PTm n) : Fm PTm n := .all
  (rationalLE (ap2 (GaussianRootDistanceCompletion.nameF step a point) (var 0)
    (GaussianRootDistanceCompletion.nameData (Syn.shift N) (Syn.shift x))) (fraction one (unit (var 0))))
def zeroStage (k : PTm n) : PTm n := (k+one)+two

ipra_subst completedZero [Syn.subst_shift, Syn.shift_subst]
ipra_subst zeroStage

theorem zero_at (step a : PR 3) (point : PR 2) (N x k : PTm n)
    (h : Γ ⊢[PRAAx] completedZero step a point N x) : Γ ⊢[PRAAx]
    rationalLE (ap2 (GaussianRootDistanceCompletion.nameF step a point) k (GaussianRootDistanceCompletion.nameData N x))
      (fraction one (unit k)) := by simpa [completedZero] using h.allE k

/-- A membership witness is used only locally; the output concerns the
fixed raw stage r and has no dependency on the existential later stage. -/
theorem raw_slack_from_stage (step a : PR 3) (point : PR 2) (N x r m t : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N x)
    (hStage : Γ ⊢[PRAAx] GaussianRootMembership.stageCondition step a point N x (m+r) t) : Γ ⊢[PRAAx]
    GaussianScalarSlackRemoval.slack (GaussianRootDistanceCompletion.raw step a point N x r) two (unit r) three m := by
  have rd := Prf.andE₁ h
  have cn := Prf.andE₁ (Prf.andE₂ h)
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have pc := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))
  have hrt := le_trans (le_add_left r m) (Prf.andE₁ hStage)
  have upper := GaussianRootDistanceCompletion.raw_stage_upper step a point N x r t m rd cn hn pc hrt
  have comparison := GaussianEuclideanDistanceName.distance_le_at point (GaussianRootRadius.roots step a N t x) x
    one (unit (m+r)) m (Prf.andE₂ hStage)
  have finite := RationalArgmin.rationalLE_congr (.eqRefl _)
    (GaussianEuclideanDistanceName.cut_fraction one (unit (m+r)) m (unit_positive (m+r))) comparison
  have source := GaussianScalarSlackRemoval.upper_cut _ _ _ _ _ _ _ _ _ _
    (GaussianEuclideanDistanceUpperCut.denominator_positive point (GaussianRootRadius.roots step a N r x) x r)
    (GaussianEuclideanDistanceUpperCut.denominator_positive point (GaussianRootRadius.roots step a N t x) x m)
    (positive_product _ _ (unit_positive r) (unit_positive m))
    (positive_product _ _ (unit_positive (m+r)) (unit_positive m))
    (GaussianEuclideanDistanceUpperCut.sample_represents point (GaussianRootRadius.roots step a N r x) x r)
    (GaussianEuclideanDistanceUpperCut.sample_represents point (GaussianRootRadius.roots step a N t x) x m) upper finite
  have order : Γ ⊢[PRAAx] le (unit m) (unit (m+r)) :=
    GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (le_add_right m r)
  have target : Γ ⊢[PRAAx] rationalLE
      (fraction ((one*unit m+unit (m+r))*(unit r*unit m)+(two*unit m+unit r)*(unit (m+r)*unit m))
        ((unit (m+r)*unit m)*(unit r*unit m)))
      (fraction (two*unit m+three*unit r) (unit r*unit m)) := GaussianEuclideanDistanceName.fraction_order _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive (m+r)) (unit_positive m))
      (positive_product _ _ (unit_positive r) (unit_positive m)))
    (positive_product _ _ (unit_positive r) (unit_positive m))
    (le_congr (by ipra_ring) (.eqRefl _) (member_query_budget (unit r) (unit m) (unit (m+r)) order))
  exact RationalArgmin.transitive source target

theorem member_raw_slack_at (step a : PR 3) (point : PR 2) (N x r m : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N x)
    (hMember : Γ ⊢[PRAAx] GaussianRootMembership.member step a point N x) : Γ ⊢[PRAAx]
    GaussianScalarSlackRemoval.slack (GaussianRootDistanceCompletion.raw step a point N x r) two (unit r) three m := by
  refine .exE (GaussianRootMembership.member_at step a point N x (m+r) hMember) ?_
  let E := GaussianRootMembership.stageCondition step a point (Syn.shift N) (Syn.shift x) (Syn.shift (m+r)) (var 0)
  have hs : E :: Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inputContract,Syn.shift] using h.shift.wk
  have stage : E :: Γ.map Fm.shift ⊢[PRAAx]
      GaussianRootMembership.stageCondition step a point (Syn.shift N) (Syn.shift x) (Syn.shift m+Syn.shift r) (var 0) := by
    simpa only [E,Syn.shift,PTm.subst_add] using (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E)
  simpa only [E,Fm.shift,GaussianScalarSlackRemoval.subst_slack,GaussianRootDistanceCompletion.subst_raw,
    subst_unit,subst_three,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    raw_slack_from_stage step a point (Syn.shift N) (Syn.shift x) (Syn.shift r) (Syn.shift m) (var 0) hs stage

theorem member_raw_slacks (step a : PR 3) (point : PR 2) (N x r : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N x)
    (hMember : Γ ⊢[PRAAx] GaussianRootMembership.member step a point N x) : Γ ⊢[PRAAx]
    GaussianScalarSlackRemoval.allSlack (GaussianRootDistanceCompletion.raw step a point N x r) two (unit r) three := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inputContract,Syn.shift] using h.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] GaussianRootMembership.member step a point (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRootMembership.subst_member,Syn.shift] using hMember.shift
  simpa only [Syn.shift,GaussianRootDistanceCompletion.subst_raw,subst_unit,subst_three,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    member_raw_slack_at step a point (Syn.shift N) (Syn.shift x) (Syn.shift r) (var 0) hs hm

theorem member_raw_bound (step a : PR 3) (point : PR 2) (N x r : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N x)
    (hMember : Γ ⊢[PRAAx] GaussianRootMembership.member step a point N x) : Γ ⊢[PRAAx]
    rationalLE (GaussianRootDistanceCompletion.raw step a point N x r) (fraction two (unit r)) :=
  GaussianScalarSlackRemoval.slack_removal _ _ _ _ _ _
    (GaussianEuclideanDistanceUpperCut.denominator_positive point (GaussianRootRadius.roots step a N r x) x r)
    (unit_positive r) (GaussianEuclideanDistanceUpperCut.sample_represents point (GaussianRootRadius.roots step a N r x) x r)
    (member_raw_slacks step a point N x r h hMember)

theorem member_to_completed_zero_at (step a : PR 3) (point : PR 2) (N x k : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N x)
    (hMember : Γ ⊢[PRAAx] GaussianRootMembership.member step a point N x) : Γ ⊢[PRAAx]
    rationalLE (ap2 (GaussianRootDistanceCompletion.nameF step a point) k (GaussianRootDistanceCompletion.nameData N x))
      (fraction one (unit k)) := by
  have small := member_raw_bound step a point N x (k+two) h hMember
  have shift : Γ ⊢[PRAAx] le (two*unit k) (unit (k+two)) := by
    simpa only [GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit,GaussianEuclideanDistanceName.shifted] using
      GaussianEuclideanDistanceName.two_units_le_shift (Γ := Γ) k
  have radius := GaussianEuclideanDistanceName.fraction_order two (unit (k+two)) one (unit k)
    (unit_positive _) (unit_positive _)
    (le_congr (by ipra_ring) (by ipra_ring) shift)
  exact RationalArgmin.rationalLE_congr (GaussianRootDistanceCompletion.name_at step a point N x k).eqSymm (.eqRefl _)
    (RationalArgmin.transitive small radius)

theorem member_to_completed_zero (step a : PR 3) (point : PR 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N x)
    (hMember : Γ ⊢[PRAAx] GaussianRootMembership.member step a point N x) : Γ ⊢[PRAAx]
    completedZero step a point N x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_inputContract,Syn.shift] using h.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] GaussianRootMembership.member step a point (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRootMembership.subst_member,Syn.shift] using hMember.shift
  exact member_to_completed_zero_at step a point (Syn.shift N) (Syn.shift x) (var 0) hs hm

/-- The zero predicate supplies a literal finite observation at the actual
stage (k+1)+2; no existential stage search is used in this direction. -/
theorem completed_zero_to_stage (step a : PR 3) (point : PR 2) (N x k : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hZero : Γ ⊢[PRAAx] completedZero step a point N x) : Γ ⊢[PRAAx]
    GaussianRootMembership.stageCondition step a point N x k (zeroStage k) := by
  let j := k+one
  let t := j+two
  let J := unit j
  let K := unit (t+two)
  have jp : Γ ⊢[PRAAx] le one J := unit_positive j
  have kp : Γ ⊢[PRAAx] le one K := unit_positive (t+two)
  have nonempty := le_congr (.eqRefl _) (GaussianRootRadius.roots_length step a N t x).eqSymm hN
  have small := RationalArgmin.rationalLE_congr (GaussianRootDistanceCompletion.name_at step a point N x j) (.eqRefl _)
    (zero_at step a point N x j hZero)
  have found := GaussianEuclideanPointDistance.lower_bound_to_hit (ap2 point (t+two) x)
    (GaussianRootRadius.roots step a N t x) (t+two) one J nonempty jp small
  have twoJ : Γ ⊢[PRAAx] le (two*J) K := le_trans (GaussianEuclideanDistanceName.two_units_le_shift j)
    (GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (le_add_right (j+two) two))
  have budget : Γ ⊢[PRAAx] le (((one*K+J)*K+J*K)*unit k) (one*((J*K)*K)) :=
    le_congr (by ipra_ring) (.eqRefl _)
      (zero_query_budget (unit k) J K (GaussianRootMembershipBudget.unit_add_one k) twoJ)
  have cut := GaussianEuclideanDistanceName.finite_hit_to_cut point (GaussianRootRadius.roots step a N t x) x (t+two)
    (one*K+J) (J*K) one (unit k) hPoint (positive_product _ _ jp kp) (unit_positive k) found budget
  exact .andI (le_trans (le_add_right k one) (le_add_right (k+one) two)) cut

theorem completed_zero_to_member (step a : PR 3) (point : PR 2) (N x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hZero : Γ ⊢[PRAAx] completedZero step a point N x) : Γ ⊢[PRAAx] GaussianRootMembership.member step a point N x := by
  refine .allI ?_
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hN.shift
  have hp : Γ.map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift x) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hPoint.shift
  have hz : Γ.map Fm.shift ⊢[PRAAx] completedZero step a point (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,subst_completedZero,Syn.shift] using hZero.shift
  exact GaussianRootMembership.precision_intro _ _ _ _ _ _ _ (completed_zero_to_stage step a point _ _ (var 0) hn hp hz)

theorem member_iff_completed_zero (step a : PR 3) (point : PR 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N x) : Γ ⊢[PRAAx]
    Fm.iff (GaussianRootMembership.member step a point N x) (completedZero step a point N x) :=
  .iffI (.impI (member_to_completed_zero _ _ _ _ _ h.wk Prf.hyp0))
    (.impI (completed_zero_to_member _ _ _ _ _ (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))).wk
      (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))).wk Prf.hyp0))

def zeroStageF : PR 1 := PTm.toPR (zeroStage (var 0))
theorem zero_stage_program (k : PTm n) : Γ ⊢[PRAAx] ap1 zeroStageF k ≐ zeroStage k := by
  simpa only [zeroStageF,ap1,subst_zeroStage,Syn.subst_var,Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (zeroStage (var 0) : PTm 1) ![k]

theorem root_distance_zero_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (inputContract step a point (var 0) (var 1) ⟶
      Fm.iff (GaussianRootMembership.member step a point (var 0) (var 1)) (completedZero step a point (var 0) (var 1))) :=
  closeUniv 2 (.impI (member_iff_completed_zero _ _ _ _ _ Prf.hyp0))

theorem distance_zero_stage_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ pointCN point (var 1) ⟶ completedZero step a point (var 0) (var 1) ⟶
      GaussianRootMembership.stageCondition step a point (var 0) (var 1) (var 2) (zeroStage (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (completed_zero_to_stage _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem distance_zero_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (ap1 zeroStageF (var 0) ≐ zeroStage (var 0)) :=
  closeUniv 1 (zero_stage_program _)

end LeanProofs.IPRA.Analysis.GaussianRootDistanceZero
